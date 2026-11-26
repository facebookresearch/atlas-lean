# Evaluation formula for signed tensor–Hom currying

Evaluation formula for signed tensor–Hom currying.

Let `a + n = b` and `c + b = d`. For `x : P.X (-a)` and `y : Q.X (-c)`, the curried cochain
evaluated in outer coordinate `(a, b)` and inner coordinate `(c, d)` equals
`Int.triangularSign b` times `f.v (a + c) d` evaluated on the total class `[x ⊗ y]` in chain
degree `-(a + c)`.
