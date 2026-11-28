# The partial derivatives of the Weierstrass polynomial after a variable change

Let `F` be
a field, let `W` be a Weierstrass curve over `F` with coefficients `a₁, a₂, a₃, a₄, a₆`, and write
`P_W(x, y) = 2y + a₁ x + a₃` and `Q_W(x, y) = 3x² + 2a₂ x + a₄ - a₁ y` in `F[x, y]`; they are
`∂f_W/∂y` and `-∂f_W/∂x` for `f_W = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`. Let
`C = (u, r, s, t)` be a variable change, with `u ∈ Fˣ` and `r, s, t ∈ F`, and let `W' = C • W`.
Then, in `F[x', y']`, with `x = u² x' + r` and `y = u³ y' + u² s x' + t`,
`P_W(x, y) = u³ P_{W'}(x', y')` and `Q_W(x, y) = u⁴ Q_{W'}(x', y') + s u³ P_{W'}(x', y')`.

Here `F[x', y']` is `F[X][Y]` with inner variable `x'` and outer variable `y'`, `P_W` is
`WeierstrassCurve.Affine.polynomialY`, `Q_W` is `-WeierstrassCurve.Affine.polynomialX`, and the
left sides evaluate the polynomials of `W` mapped to `F[X][Y]` by constants at `x` and `y`.

## Sources

- J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52, for the variable change and the coefficients of `W'`; the identities follow by expansion.
