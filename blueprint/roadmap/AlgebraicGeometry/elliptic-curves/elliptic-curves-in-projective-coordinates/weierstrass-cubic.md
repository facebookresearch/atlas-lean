# Weierstrass Cubic

The monic cubic in one variable `T` over `MvPolynomial (Fin 2) F` whose polynomial `toPoly`
is the negative of the image of the projective Weierstrass polynomial under `finSuccEquiv F 2`
(`finSuccEquiv_polynomial`). That equivalence sends `X 0` to `T` and `X 1`, `X 2` to the
coefficient variables `X 0`, `X 1`; writing `Y`, `Z` for these, the polynomial is
$T^3 + a_2 Z T^2 + (a_4 Z^2 - a_1 Y Z) T + (a_6 Z^3 - Y^2 Z - a_3 Y Z^2)$.
No coordinate is set to `1`, so this is not a dehomogenization: it rewrites the same
homogeneous cubic with `X 0` separated.
