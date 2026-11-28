# The partial derivatives of a nonsingular Weierstrass polynomial generate the unit ideal

Let `F` be a field and let `W` be a Weierstrass curve over `F` with coefficients
`a₁, a₂, a₃, a₄, a₆` and discriminant `Δ_W ≠ 0`. Let
`A_W = F[x, y] / (y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆)` be its affine coordinate ring.
Then the classes of `P_W = 2y + a₁ x + a₃` and `Q_W = 3x² + 2a₂ x + a₄ - a₁ y` (that is,
`∂f/∂y` and `-∂f/∂x` for the defining polynomial `f`) generate the unit ideal of `A_W`: there
are `p, q ∈ A_W` with `p P_W + q Q_W = 1`.

Here `A_W` is `WeierstrassCurve.Affine.CoordinateRing`, `P_W` is
`WeierstrassCurve.Affine.polynomialY` and `Q_W` is `-WeierstrassCurve.Affine.polynomialX`.

## Sources

- J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(a), p. 52: the curve of a Weierstrass equation is nonsingular if and only if `Δ ≠ 0`. The algebraic form is proved here: a maximal ideal containing both classes would give a singular point of `W` over its residue field.
