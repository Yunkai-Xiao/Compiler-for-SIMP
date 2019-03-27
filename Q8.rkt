#lang racket
;-------------- Compiler from SIMP to A-PRIMP
(define memsize 10000)
(define memory (make-vector memsize 0))
(define SP 0)
(define temcounter 1)
(define labelcounter 1)
(define dataset (mutable-set))

(define dispatchtable
  (hash
   '+ 'add
   '- 'sub
   '* 'mul
   'div 'div
   'mod 'mod
   '= 'equal
   '> 'gt
   '< 'lt
   '>= 'ge
   '<= 'le
   'not 'lnot
   'and 'land
   'or 'lor
   ))

(define (solve-op target op) ;;e.g: y, (* 2 (+ 2 3)) returns a list of aprimp instructions
  (cond
    [(not (list? op)) (solve-op target (list '* 1 op))]
    [(and (list? (second op))(list? (third op)))
     (begin
       (vector-set! memory SP (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
       (set! SP (+ 1 SP))
       (set! temcounter (+ 1 temcounter))
       (vector-set! memory SP (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
       (set! SP (+ 1 SP))
       (set! temcounter (+ 1 temcounter))
       (set-add! dataset (list 'data (string->symbol(string-append* "TMP" (list (number->string (- temcounter 2))))) 0))
       (set-add! dataset (list 'data (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) 0))
       (append (list (list (hash-ref dispatchtable (first op)) target
                           (string->symbol(string-append* "TMP" (list (number->string (- temcounter 2)))))
                           (string->symbol(string-append* "TMP" (list (number->string (sub1 temcounter)))))))
               (solve-op (string->symbol(string-append* "TMP" (list (number->string (- temcounter 2))))) (second op))
               (solve-op (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) (third op))))]
    [(list? (second op))
     (begin
       (vector-set! memory SP (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
       (set! SP (+ 1 SP))
       (set! temcounter (+ 1 temcounter))
       (set-add! dataset (list 'data (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) 0))
       (append (list (list (hash-ref dispatchtable (first op)) target
                           (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1)))))
                           (third op)))
               (solve-op (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) (second op))))]
    [(list? (third op))
     (begin
       (vector-set! memory SP (string->symbol(string-append* "TMP" (list (number->string temcounter)))))
       (set! SP (+ 1 SP))
       (set! temcounter (+ 1 temcounter))
       (set-add! dataset (list 'data (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) 0))
       (append (list (list (hash-ref dispatchtable (first op)) target
                           (second op)
                           (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1)))))))
               (solve-op (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) (third op))))]
    [true (list (list (hash-ref dispatchtable (first op)) target (second op) (third op)))]  
    ))


(define (compile-simp explst)
  (define (solvevar varlst) ;a void function
    (if (empty? varlst) empty
        (begin
          (set-add! dataset (list 'data (first (car varlst)) (second (car varlst))))
          (solvevar (cdr varlst)))))
  (define (solveif con stmt1 stmt2)
    (begin
      (set! temcounter (add1 temcounter))
      (define lst1 (solve-op (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1)))))con))
      (define lst2 (list 'branch (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1)))))
                         (string->symbol(string-append* "label" (list (number->string labelcounter))))))
      (set-add! dataset (list 'data (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) 0))
      (define lst3 (list 'jump (string->symbol(string-append* "label" (list (number->string (+ 1 labelcounter)))))))
      (define lst4 (list 'label (string->symbol(string-append* "label" (list (number->string labelcounter))))))
      (define stmt1-code (solveseq stmt1 empty))
      (define lst5 (list 'jump (string->symbol(string-append* "label" (list (number->string (+ 2 labelcounter)))))))
      (define lst6 (list 'label (string->symbol(string-append* "label" (list (number->string (+ 1 labelcounter)))))))
      (define stmt2-code (solveseq stmt2 empty))
      (define lst7 (list 'label (string->symbol(string-append* "label" (list (number->string (+ 2 labelcounter)))))))
      (append lst1 (list lst2 lst3 lst4) stmt1-code (list lst5 lst6) stmt2-code (list lst7))
      ))
  (define (solvewhile con stmts);a list of statements to be executed in the while loop.
    (begin
      (set! temcounter (add1 temcounter))
      (define lst0 (list 'label (string->symbol(string-append* "label" (list (number->string labelcounter))))))
      (define lst1 (solve-op (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1)))))con))
      (define lst2 (list 'branch (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1)))))
                         (string->symbol(string-append* "label" (list (number->string (add1 labelcounter)))))))
      (set-add! dataset (list 'data (string->symbol(string-append* "TMP" (list (number->string (- temcounter 1))))) 0))
      (define lst3 (list 'jump (string->symbol(string-append* "label" (list (number->string (+ 2 labelcounter)))))))
      (define lst4 (list 'label (string->symbol(string-append* "label" (list (number->string (add1 labelcounter)))))))
      (define lst5 (list 'jump (string->symbol(string-append* "label" (list (number->string labelcounter))))))
      (define lst6 (list 'label (string->symbol(string-append* "label" (list (number->string (+ 2 labelcounter)))))))
      (set! labelcounter (+ 3 labelcounter))
      (append (list lst0) lst1 (list lst2 lst3 lst4)(solveseq stmts empty)(list lst5 lst6))))
  (define (solveseq lst acc)
    (cond
      [(empty? lst) acc]
      [(symbol? (car lst)) (cs-h lst empty)]
      [true (solveseq (cdr lst) (append acc (cs-h (car lst) empty)))]))
  (define (cs-h explst aprimplst)
    (if (empty? explst) true
        (match explst
          [`(vars ,a ,b) (cs-h b (solvevar a))]
          [`(vars ,a ,stmts ___) (cs-h (cons 'seq stmts) (solvevar a))]
          [`(set ,a ,b) (append aprimplst (solve-op a b))]
          [`(while ,con ,stmts ...)(append aprimplst (solvewhile con stmts))]
          [`(seq ,val ___) (append aprimplst (solveseq val empty))]
          [`(print ,a) (if (string? a) (append aprimplst (list(list 'print-string a)))
                           (append aprimplst (list(list 'print-val a))))]
          [`(skip) aprimplst]
          [`(iif ,con ,stmt1 ,stmt2) (append aprimplst (solveif con stmt1 stmt2))]
          ))) 
  (append (cs-h explst empty)(set->list dataset))
  )


(define test '(vars [(x 10) (y 1)]  
                    (iif (> 2 1)
                         ((print x)(print 2))
                         ((print y)))))

(define test1 '(vars [(x 10) (y 1) (z 5)]
                     (iif (> 2 1)
                          (while (> x 5)
                                 (print "x is now greater than 5")
                                 (set x (- x 1)))
                          (print "x is smaller than 5"))))



(define test2 '(vars [(x 100) (y 200) (z 300) (t 400)]
                     (while (< x t)
                            (set x y)
                            (set z (+ 2 (* z t)))
                            (set y 10)
                            (print "hello-word"))
                     (set x (+ x t))
                     (set t (mod 5 x))
                     (print x)
                     ))






