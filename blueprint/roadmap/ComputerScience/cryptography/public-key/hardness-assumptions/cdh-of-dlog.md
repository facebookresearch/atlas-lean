# Cdh Of Dlog

The CDH solver built from a discrete-logarithm solver `A` (Katz and Lindell, Section 8.3.2:
"if the discrete-logarithm problem is easy, so is CDH"): on `(X, Y)` it computes
`x' = A X` and outputs `Y ^ x'`.
