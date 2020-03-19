;
; RISC-V Assembler - 20th March 2020
; see http://www.ulisp.com/show?310Z
;

; Print 16-bit number in hex
(defun x16 (n)
  (printhex 4 n))

; Print 32-bit number in hex
(defun x32 (n)
  (printhex 8 n))

(defun printhex (m n)
  (princ "#x")
  (dotimes (j m nil)
    (let ((d (logand (ash n (* (- j m -1) 4)) #xf)))
      (princ
       (code-char (+ d (if (< d 10) (char-code #\0) (char-code #\W))))))))

; Extract register number
(defun regno (sym)
  (case sym (zero 0) (ra 1) (sp 2) (gp 3) (tp 4) (s0 8) (fp 8) (s1 9)
    (t (let* ((s (string sym))
              (c (char s 0))
              (n (read-from-string (subseq s 1))))
         (case c (#\x n) (#\a (+ n 10)) (#\s (+ n 16)) (#\t (if (<= n 2) (+ n 5) (+ n 25))))))))

; Short 3-bit register
(defun cregp (rd) (<= 8 (regno rd) 15))

(defun cregno (sym) (logand (regno sym) #x7))

; Pack arguments into bit fields
(defun emit (bits &rest args)
  (let ((word 0))
    (mapc #'(lambda (width value)
              (unless (zerop (ash value (- width))) (error* "Won't fit"))
              (setq word (logior (ash word width) value)))
          bits args)
    word))

; 32-bit emit
(defun emit* (bits &rest args)
  (let ((word (apply #'emit bits args)))
    (list (logand word #xffff) (logand (ash word -16) #xffff))))

; Errors
(defun error* (txt) (princ "(pc=") (x16 *pc*) (princ ") ") (princ txt) (terpri))

; Test range of immediate values
(defun immp (x b)
  (<= (- (ash 1 (1- b))) x (1- (ash 1 (1- b)))))

; Extract bitfield
(defun bits (x a &optional b)
  (if b (logand (ash x (- b)) (1- (ash 1 (- a b -1))))
    (logand (ash x (- a)) 1)))

(defun offset (label) (- label *pc*))

; Instruction formats

(defun register (funct7 rs2 rs1 funct3 rd op)
  (emit* '(7 5 5 3 5 7) funct7 (regno rs2) (regno rs1) funct3 (regno rd) op))

(defun cregister (op3 op1 op2 rd op2b rs2)
  (cond
   ((and (cregp rd) (cregp rs2))
    (emit '(3 1 2 3 2 3 2) op3 op1 op2 (cregno rd) op2b (cregno rs2) 1))
   (t (error* "C won't fit"))))

(defun immed (imm12 rs1 funct3 rd op)
  (cond
   ((immp imm12 12)
    (emit* '(12 5 3 5 7) (logand imm12 #xfff) (regno rs1) funct3 (regno rd) op))
   (t
    (error* "Immediate value out of range"))))

(defun cimmed (imm12 rs1 funct3 rd op)
  (emit* '(12 5 3 5 7) imm12 (regno rs1) funct3 (regno rd) op))

(defun branch (imm12 rs2 rs1 funct3 funct7)
  (let ((off (offset imm12)))
    (emit* '(1 6 5 5 3 4 1 7) 
           (bits off 12) (bits off 10 5) (regno rs2) 
           (regno rs1) funct3 (bits off 4 1) (bits off 11) funct7)))

(defun jump (imm20 imm10-1 imm11 imm19-12 rd op)
  (emit* '(1 10 1 8 5 7) imm20 imm10-1 imm11 imm19-12 rd op))

(defun muldiv (rs2 rs1 funct3 rd funct7)
  (emit* '(7 5 5 3 5 7) 1 (regno rs2) (regno rs1) funct3 (regno rd) funct7))

(defun store (imm src base op)
  (emit* '(7 5 5 3 5 7) (bits imm 11 5) (regno src) (regno base) op (bits imm 4 0) #x23))

(defun cimm6 (rd imm op1 op2)
  (emit '(3 1 5 5 2) op1 (bits imm 5) (regno rd) (bits imm 4 0) op2))

(defun cimm6* (rd imm op1 op2 op3)
  (emit '(3 1 2 3 5 2) op1 (bits imm 5) op2 (cregno rd) (bits imm 4 0) op3))

;
; Alphabetical list of mnemonics
;

(defun $add (rd rs1 rs2)
  (cond
   ((eq rd rs1)
    (emit '(3 1 5 5 2) 4 1 (regno rd) (regno rs2) 2))
   (t (register 0 rs2 rs1 0 rd #x33))))

(defun $addi (rd rs1 imm)
  (cond
   ((and (eq rd rs1) (immp imm 6))
    (cimm6 rd imm 0 1))
   ((and (= (regno rd) 2) (= (regno rs1) 2) (immp imm 10))
    (emit '(3 1 5 1 1 2 1 2) 3 (bits imm 9) 2 (bits imm 4) (bits imm 6) (bits imm 8 7) (bits imm 5) 1))
   (t (immed imm rs1 0 rd #x13))))

(defun $addiw (rd rs1 imm)
  (cond
   ((and (eq rd rs1) (immp imm 5))
    (cimm6 rd imm 1 1))
   (t (immed imm rs1 0 rd #x1b))))

(defun $addw (rd rs1 rs2)
 (cond
  ((and (eq rd rs1) (cregp rd) (cregp rs2))
    (cregister 4 1 3 rd 1 rs2))
  (t (register 0 rs2 rs1 0 rd #x3b))))

(defun $and (rd rs1 rs2)
  (cond
   ((and (eq rd rs1) (cregp rd) (cregp rs2))
    (cregister 4 0 3 rd 3 rs2))
   (t (register 0 rs2 rs1 7 rd #x33))))

(defun $andi (rd rs1 imm)
  (cond
   ((and (eq rd rs1) (cregp rd) (immp imm 5))
    (cimm6* rd imm 4 2 1))
   (t (immed imm rs1 7 rd #x13))))

(defun $auipc (rd imm)
  (cond
   ((zerop (logand imm #xfff))
    (emit* '(20 5 7) (bits imm 31 12) (regno rd) #x17))
   (t (error* "auipc no good"))))

(defun $beq (rs1 rs2 imm12)
  (branch imm12 rs2 rs1 0 #x63))

(defun $beqz (rs imm)
  (let ((off (offset imm)))
    (cond
     ((and (immp off 8) (cregp rs))
      (emit '(3 1 2 3 2 2 1 2) 6 (bits off 8) (bits off 4 3) 
            (cregno rs) (bits off 7 6) (bits off 2 1) (bits off 5) 1))
     (t ($beq rs 'x0 imm)))))
    
(defun $ble (rs1 rs2 imm12)
  ($bge rs2 rs1 imm12))

(defun $bne (rs1 rs2 imm12)
  (branch imm12 rs2 rs1 1 #x63))

(defun $bnez (rs imm)
  (let ((off (offset imm)))
    (cond
     ((and (immp off 8) (cregp rs))
      (emit '(3 1 2 3 2 2 1 2) 7 (bits off 8) (bits off 4 3) 
            (cregno rs) (bits off 7 6) (bits off 2 1) (bits off 5) 1))
     (t ($bne rs 'x0 imm)))))

(defun $bge (rs1 rs2 imm12)
  (branch imm12 rs2 rs1 5 #x63))

(defun $bgez (rs1 imm12)
  ($bge rs1 'x0 imm12))

(defun $bgtz (rs1 imm12)
  ($blt 'x0 rs1 imm12))

(defun $blt (rs1 rs2 imm12)
  (branch imm12 rs2 rs1 4 #x63))

(defun $bltu (rs1 rs2 imm12)
  (branch imm12 rs2 rs1 6 #x63))

(defun $bltz (rs1 imm12)
  ($blt rs1 'x0 imm12))

(defun $bgeu (rs1 rs2 imm12)
  (branch imm12 rs2 rs1 7 #x63))

(defun $bleu (rs1 rs2 imm12)
  ($bgeu rs2 rs1 imm12))

(defun $blez (rs1 imm12)
  ($bge 'x0 rs1 imm12))

(defun $div (rd rs1 rs2)
  (muldiv rs2 rs1 4 rd #x33)) 

(defun $divu (rd rs1 rs2)
  (muldiv rs2 rs1 5 rd #x33))

(defun $divw (rd rs1 rs2)
  (muldiv rs2 rs1 4 rd #x3b))

(defun $divuw (rd rs1 rs2)
  (muldiv rs2 rs1 5 rd #x3b))

(defun $fence () (emit* '(16 16) #x0ff0 #x000f))

(defun $j (label)
  (let ((off (offset label)))
      (emit '(3 1 1 2 1 1 1 3 1 2) 5 (bits off 11) (bits off 4) (bits off 9 8)
          (bits off 10) (bits off 6) (bits off 7) (bits off 3 1) (bits off 5) 1)))

; C.JAL is RV32 only
(defun $jal (rd &optional label)
  (when (null label) (setq label rd rd 'ra))
  (let ((off (offset label)))
    (emit* '(1 10 1 8 5 7) (bits off 20) (bits off 10 1) (bits off 11) (bits off 19 12) (regno rd) #x6f)))

(defun $jalr (label lst)
  (let ((off (+ (offset label) 4)))
    (emit* '(12 5 3 5 7) (bits off 11 0) (regno (car lst)) 0 (regno (car lst)) #x67)))

(defun $jr (rs1)
  (emit '(3 1 5 5 2) 4 0 (regno rs1) 0 2))

(defun $lb (rd imm lst)
  (cond
   ((listp lst)
    (immed imm (car lst) 0 rd 3))))

(defun $lbu (rd imm lst)
  (cond
   ((listp lst)
    (immed imm (car lst) 4 rd 3))))

(defun $ld (rd imm lst)
  (cond
   ; rs1 = sp
   ((and (listp lst) (= (regno (car lst)) 2) (zerop (logand imm #xfe07)))
    (emit '(3 1 5 2 3 2) 3 (bits imm 5) (regno rd) (bits imm 4 3) (bits imm 8 6) 2))
   ; rs1 = general
   ((and (listp lst) (zerop (logand imm #xff07)) (cregp (car lst)) (cregp rd))
    (emit '(3 3 3 2 3 2) 3 (bits imm 5 3) (cregno (car lst)) (bits imm 7 6) (cregno rd) 0))
   ((listp lst)
    (immed imm (car lst) 3 rd 3))))

(defun $lh (rd imm lst)
  (cond
   ((listp lst)
    (immed imm (car lst) 1 rd 3))))

(defun $lhu (rd imm lst)
  (cond
   ((listp lst)
    (immed imm (car lst) 5 rd 3))))

; li pseudoinstruction - will load 32-bit immediates
(defun $li (rd imm)
  (cond
   ((immp imm 6)
    (cimm6 rd imm 2 1))
   (t (let ((imm12 (logand imm #x00000fff))
            (imm20 (logand imm #xfffff000)))
        (append
         ($lui rd (if (= (logand imm12 #x800) #x800) (+ imm20 #x1000) imm20))
         ; $addi
         (emit* '(12 5 3 5 7) imm12 (regno rd) 0 (regno rd) #x13))))))

(defun $lui (rd imm)
  (cond
   ((zerop (logand imm #xfff))
    (emit* '(20 5 7) (bits imm 31 12) (regno rd) #x37))
   (t (error* "lui no good"))))

(defun $lw (rd imm lst)
  (cond
   ((listp lst)
    (let ((base (car lst)))
      (cond
       ; rs1 = sp
       ((and (= (regno base) 2))
        (emit '(3 1 5 3 2 2) 2 (bits imm 5) (regno rd) (bits imm 4 2) (bits imm 7 6) 2))
       ; rs1 = general
       ((and (cregp rd) (cregp base))
        (emit '(3 3 3 1 1 3 2) 2 (bits imm 5 3) (cregno base) (bits imm 2) (bits imm 6) (cregno rd) 0))
       (t (immed imm base 2 rd 3)))))
   (t (error* "Illegal 3rd arg"))))

(defun $lwu (rd imm lst)
  (cond
   ((listp lst)
    (immed imm (car lst) 6 rd 3))))

(defun $mul (rd rs1 rs2)
  (muldiv rs2 rs1 0 rd #x33))

(defun $mulh (rd rs1 rs2)
  (muldiv rs2 rs1 1 rd #x33))  

(defun $mulhsu (rd rs1 rs2)
  (muldiv rs2 rs1 2 rd #x33)) 

(defun $mulhu (rd rs1 rs2)
  (muldiv rs2 rs1 3 rd #x33))

(defun $mulw (rd rs1 rs2)
  (muldiv rs2 rs1 0 rd #x3b))

(defun $mv (rd rs1)
  (emit '(3 1 5 5 2) 4 0 (regno rd) (regno rs1) 2))

(defun $nop ()
  ($addi 'x0 'x0 0))

(defun $or (rd rs1 rs2)
  (cond
   ((and (eq rd rs1) (cregp rd) (cregp rs2))
    (cregister 4 0 3 rd 2 rs2))
   (t (register 0 rs2 rs1 6 rd #x33))))

(defun $ori (rd rs1 imm)
  (immed imm rs1 6 rd #x13))

(defun $rem (rd rs1 rs2)
  (muldiv rs2 rs1 6 rd #x33))

(defun $remu (rd rs1 rs2)
  (muldiv rs2 rs1 7 rd #x33))

(defun $remw (rd rs1 rs2)
  (muldiv rs2 rs1 6 rd #x3b)) 

(defun $remuw (rd rs1 rs2)
  (muldiv rs2 rs1 7 rd #x3b)) 

(defun $ret ()
  ($jr 'ra))

(defun $sb (src imm lst)
  (cond
   ((listp lst)
    (store imm src (car lst) 0))))

(defun $sd (src imm lst)
  (cond
   ((listp lst)
    (let ((base (car lst)))
      (cond
       ; base = sp
       ((and (= (regno base) 2) (zerop (logand imm #xfe07)))
        (emit '(3 3 3 5 2) 7 (bits imm 5 3) (bits imm 8 6) (regno src) 2))
       ; base = general
       ((and (cregp src) (cregp base))
        (emit '(3 3 3 2 3 2) 7 (bits imm 5 3) (cregno base) (bits imm 7 6) (cregno src) 0))
       (t (store imm src base 3)))))
    (t (error* "Illegal 3rd arg"))))

(defun $sext.w (rd rs)
  ($addiw rd rs 0))

(defun $sh (src imm lst)
  (cond
   ((listp lst)
    (store imm src (car lst) 1))))

(defun $sll (rd rs1 rs2)
  (register 0 rs2 rs1 1 rd #x33))

(defun $slli (rd rs1 imm)
  (cond
   ((and (eq rd rs1))
    (cimm6 rd imm 0 2))
   (t (emit* '(6 6 5 3 5 7) 0 imm (regno rs1) 1 (regno rd) #x13))))

(defun $sllw (rd rs1 rs2)
  (register 0 rs2 rs1 1 rd #x3b))

(defun $slt (rd rs1 rs2)
  (register 0 rs2 rs1 2 rd #x33))

(defun $sra (rd rs1 rs2)
  (register #x20 rs2 rs1 2 rd #x33))

(defun $srai (rd rs1 imm)
  (cond
   ((and (eq rd rs1) (cregp rd))
    (cimm6* rd imm 4 1 1))
   (t (emit* '(6 6 5 3 5 7) #x10 imm (regno rs1) 5 (regno rd) #x13))))

(defun $sraw (rd rs1 rs2)
  (register #x20 rs2 rs1 5 rd #x3b))

(defun $srl (rd rs1 rs2)
  (register 0 rs2 rs1 5 rd #x33))

(defun $srli (rd rs1 imm)
  (cond
   ((and (eq rd rs1) (cregp rd))
    (cimm6* rd imm 4 0 1))
   (t (emit* '(6 6 5 3 5 7) 0 imm (regno rs1) 5 (regno rd) #x13))))

(defun $srlw (rd rs1 rs2)
  (register 0 rs2 rs1 5 rd #x3b))

(defun $sub (rd rs1 rs2)
  (cond
   ((and (eq rd rs1) (cregp rd) (cregp rs2))
    (cregister 4 0 3 rd 0 rs2))
   (t (register #x20 rs2 rs1 0 rd #x33))))

(defun $subw (rd rs2)
  (cond
   ((and (eq rd rs1) (cregp rd) (cregp rs2))
    (cregister 4 1 3 rd 0 rs2))
   (t (register #x20 rs2 rs1 0 rd #x3b))))

(defun $sw (src imm lst)
  (cond
   ((listp lst)
    (let ((base (car lst)))
      (cond
       ; base = sp
       ((and (= (regno base) 2))
        (emit '(3 4 2 5 2) 6 (bits imm 5 2) (bits imm 7 6) (regno src) 2))
       ; base = general
       ((and (cregp src) (cregp base))
        (emit '(3 3 3 1 1 3 2) 6 (bits imm 5 3) (cregno base) (bits imm 2) (bits imm 6) (cregno src) 0))
       (t (store imm src base 2)))))
   (t (error* "Illegal 3rd arg"))))

(defun $xor (rd rs1 rs2)
  (cond
   ((and (eq rd rs1) (cregp rd) (cregp rs2))
    (cregister 4 0 3 rd 1 rs2))
   (t (register 0 rs2 rs1 4 rd #x33))))

(defun $xori (rd rs1 imm)
  (immed imm rs1 4 rd #x13))



