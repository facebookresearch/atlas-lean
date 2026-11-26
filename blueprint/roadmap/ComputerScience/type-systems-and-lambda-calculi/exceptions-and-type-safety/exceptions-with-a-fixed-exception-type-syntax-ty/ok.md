# Call-by-value frames

A frame is admissible for left-to-right call-by-value evaluation
when its hole is the leftmost unevaluated position: in `f □` the function `f` and in `a * □` the
operand `a` are values; every other frame is admissible.
