# Capped Triangular Secant

Capped-triangular front speed bounds. For the flux
`q(k) = min (v * k) (min (w * (kj - k)) Qmax)` with `v, w, kj > 0`
and `Qmax ≥ 0`, every secant slope between distinct densities in
`[0, kj]` lies between `-w` and `v`: the rising branch has slope
`v`, the falling branch slope `-w`, and the capacity plateau slope
`0`, and taking pointwise minima cannot produce a steeper secant,
including secants that cross a corner or the plateau.
