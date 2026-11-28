# The Weierstrass polynomial in the chart at infinity

Let `W` be a Weierstrass curve over a
commutative ring `R` with coefficients `a₁, a₂, a₃, a₄, a₆`. Its polynomial at infinity is
`h(z, w) = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` in `R[z, w]`, the projective
equation `Y² Z + a₁ X Y Z + a₃ Y Z² - X³ - a₂ X² Z - a₄ X Z² - a₆ Z³` read at `Y = 1`, `X = z`,
`Z = w`. Here `R[z, w]` is `MvPolynomial (Fin 2) R`, with `z` the variable `0` and `w` the
variable `1`.
