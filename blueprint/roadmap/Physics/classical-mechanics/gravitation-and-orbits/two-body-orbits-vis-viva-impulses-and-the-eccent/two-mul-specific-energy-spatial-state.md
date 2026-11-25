# The planar energy is twice the specific energy of the spatial state

For every rotation matrix `Q ∈ SO(3)`, every real `μ`, real functions `x, y, vx, vy` of time and
every time `t`, let `X = Q (x(t), y(t), 0)` and `V = Q (vx(t), vy(t), 0)` be the
[spatial position and velocity](spatial-state.md). Twice the [specific energy](specific-energy.md)
of the state `(X, V)` is the planar energy:
`2 (|V|² / 2 − μ / |X|) = vx(t)² + vy(t)² − 2 μ / √(x(t)² + y(t)²)`, with `|V|² = V · V` and
`|X| = √(X · X)`; the factor two of the planar normalization stays explicit. At a time with
`x(t) = y(t) = 0`, the convention `c / 0 = 0` makes both sides `vx(t)² + vy(t)²`. In the physical
reading `μ > 0`; the identity holds for every real `μ`.
