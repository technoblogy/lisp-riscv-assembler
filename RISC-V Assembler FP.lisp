;
; RISC-V Assembler - Floating-Point Extensions - 1st April 2020
; see http://forum.ulisp.com/t/mandelbrot-set-using-risc-v-assembler/522
;

; Extract register number
(defun regno (sym)
  (case sym (zero 0) (ra 1) (sp 2) (gp 3) (tp 4) (s0 8) (fp 8) (s1 9)
    (t (let* ((s (string sym))
              (c (char s 0)))
         (case c
           (#\f 
            (let ((c (char s 1))
                  (n (read-from-string (subseq s 2))))
              (case c (#\t (if (<= n 7) n (+ n 20))) 
                (#\s (if (<= n 1) (+ n 8) (+ n 16))) (#\a (+ n 10)))))
           (t
            (let ((n (read-from-string (subseq s 1))))
              (case c (#\x n) (#\a (+ n 10)) (#\s (+ n 16)) 
                (#\t (if (<= n 2) (+ n 5) (+ n 25)))))))))))


(defun fmuldiv (op rs2 rs1 funct3 rd funct7)
  (emit* '(7 5 5 3 5 7) op (regno rs2) (regno rs1) funct3 (regno rd) funct7))

(defun fstore (imm src base op funct7)
  (emit* '(7 5 5 3 5 7) (bits imm 11 5) (regno src) (regno base) op (bits imm 4 0) funct7))

(defun $fadd.s (rd rs1 rs2)
  (fmuldiv #x00 rs2 rs1 7 rd #x53))

(defun $fcvt.s.w (rd rs1)
  (fmuldiv #x68 'x0 rs1 7 rd #x53))

(defun $fcvt.w.s (rd rs1)
  (fmuldiv #x60 'x0 rs1 7 rd #x53))

(defun $fdiv.s (rd rs1 rs2)
  (fmuldiv #x0c rs2 rs1 7 rd #x53))

(defun $flw (rd imm lst)
  (cond
   ((listp lst)
    (immed imm (car lst) 2 rd #x07))))

(defun $fmul.s (rd rs1 rs2)
  (fmuldiv #x08 rs2 rs1 7 rd #x53))

(defun $fsub.s (rd rs1 rs2)
  (fmuldiv #x04 rs2 rs1 7 rd #x53))

(defun $fsw (src imm lst)
  (cond
   ((listp lst)
    (fstore imm src (car lst) 2 #x27))))

(defun $fsgnj.s (rd rs1 rs2)
  (fmuldiv #x10 rs2 rs1 0 rd #x53))

(defun $fsgnjn.s (rd rs1 rs2)
  (fmuldiv #x10 rs2 rs1 1 rd #x53))

(defun $fsgnjx.s (rd rs1 rs2)
  (fmuldiv #x10 rs2 rs1 2 rd #x53))

(defun $fmv.s (rd rs)
  ($fsgnj.s rd rs rs))



