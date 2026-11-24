# Source-free vacuum Maxwell equations for fields on space and time

For a speed of light `c > 0` and fields `E, B : Time → Space → ℝ³` (with values in three-dimensional
Euclidean space), for every time `t` and point `x`: `div E(t) = 0`, `div B(t) = 0`,
`curl E(t) = −∂_t B` and `curl B(t) = c⁻² ∂_t E` at `x`. The divergence and curl are taken in
space: each partial derivative is the derivative of the component as a function of position along
the coordinate direction, taken to be `0` where that component is not differentiable as a function
of position (even if the partial derivative exists). The time derivative `∂_t B` at `(t, x)` is the
derivative at `t` of the whole field `s ↦ B(s, x)`, taken to be `0` where that vector-valued
function is not differentiable in time, and likewise for `∂_t E`.
