# The Weierstrass polynomial after a variable change

Let `F` be a field, let `W` be a
Weierstrass curve over `F` with coefficients `a₁, a₂, a₃, a₄, a₆`, and let
`f_W(x, y) = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`. Let `C = (u, r, s, t)` be a variable
change, with `u ∈ Fˣ` and `r, s, t ∈ F`, and let `W' = C • W`. Then, in the polynomial ring
`F[x', y']`, `f_W(u² x' + r, u³ y' + u² s x' + t) = u⁶ f_{W'}(x', y')`.

Here `F[x', y']` is `F[X][Y]` with inner variable `x'` and outer variable `y'`, `f_W` is
`WeierstrassCurve.Affine.polynomial`, and the left side evaluates the polynomial of `W` mapped to
`F[X][Y]` by constants at `u² x' + r` and `u³ y' + u² s x' + t`.

## Sources

- J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52: the isomorphism `(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)` between the curves of the two equations, with the coefficients of `W'`; the identity follows by expansion.
