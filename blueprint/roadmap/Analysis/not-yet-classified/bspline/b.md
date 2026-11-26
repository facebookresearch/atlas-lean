# B

B-spline basis by Cox-de Boor: `B t i k` is the degree-`k` basis
function on the knots `t` (de Boor's `N_{i,k+1}`), and degree `0` is the
indicator of `[t i, t (i + 1))`. A recursion term whose knot-span
denominator is zero, as at repeated knots, contributes zero regardless of
its numerator, because Lean's real division gives `a / 0 = 0`.
