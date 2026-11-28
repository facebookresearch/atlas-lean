# The two charts agree on their overlap

Let `W` be a Weierstrass curve over a commutative
ring `R`, with affine coordinate ring `A_W = R[x, y] / (g)`,
`g = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`, and coordinate ring at infinity
`B_W = R[z, w] / (h)`, `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`. Then there is
an isomorphism of `R`-algebras `A_W[1 / y] ≃ B_W[1 / w]` sending `x ↦ z / w` and `y ↦ 1 / w`; its
inverse sends `z ↦ x / y` and `w ↦ 1 / y` (`awayYEquivAwayW_affineX`, `awayYEquivAwayW_affineY`,
`awayYEquivAwayW_symm_zAtInfinity`, `awayYEquivAwayW_symm_wAtInfinity`). It identifies the two
charts of the projective curve on their overlap `Y Z ≠ 0`.

The source states this over a field with `Δ_W ≠ 0`; neither hypothesis is used: `R` is any
commutative ring and `W` any Weierstrass curve.

## Sources

- J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version <https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34: a projective plane curve is written "as a union of affine curves $C = C_0 \cup C_1 \cup C_2$ in the usual way"; B. Conrad, *Minimal models for elliptic curves*, 2015, <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, §2, (2.1), p. 2, the projective planar Weierstrass curve.
