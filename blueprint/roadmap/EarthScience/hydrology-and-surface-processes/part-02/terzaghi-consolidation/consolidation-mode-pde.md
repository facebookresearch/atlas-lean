# The consolidation mode solves the Terzaghi consolidation equation

For a layer thickness `H ≠ 0` and all real `u0` and `cv`, the
[consolidation mode](consolidation-mode.md)
`u(z, t) = u0 * exp (-cv * (π / H) ^ 2 * t) * sin (π * z / H)` satisfies the one-dimensional
Terzaghi consolidation equation `∂u/∂t = cv * ∂²u/∂z²` at every time `t` and depth `z`.
