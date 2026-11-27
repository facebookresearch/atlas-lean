# Side-wall force on a steady flow through a box is the thrust

Let `[a, b] ⊂ ℝⁿ⁺¹` be a box with `a_i < b_i` for every `i`, contained in an open set `U`, and fix a
time `t`. Let `ρ` (density) and `v` (velocity) be continuously differentiable in `(τ, x)`, let the
Cauchy stress `σ(t)` (with `σ_{ji}` the `j`-th traction component on a surface of unit normal `eᵢ`)
be continuously differentiable on `U`, and let every component of the body force `f(t)` be
integrable on the box. Assume:

- the local momentum law `∂_τ(ρ v_j) + div(ρ v_j v − σ_{j·}) = f_j` at time `t` at every point of
  the box, for every `j`;
- uniform pressure-only port data: on the inlet face `x₀ = a₀`, `ρ = ρ_in`, `v = v_in` and
  `σ_{j0} = −p_in δ_{j0}`; on the exhaust face `x₀ = b₀`, `ρ = ρ_out`, `v = v_out` and
  `σ_{j0} = −p_out δ_{j0}`;
- impermeable side walls: for every `i ≠ 0`, the `i`-th velocity component vanishes on both
  faces normal to `eᵢ`;
- stationary momentum, `d/dτ ∫ ρ v = 0` at `τ = t` over the box, and no axial body force,
  `∫ f₀ = 0` over the box.

Then for every ambient pressure `p_a`, the axial (`+e₀`, inlet to exhaust) component of the traction
resultant of the side walls on the fluid, over the side faces (the sum over `i ≠ 0` of the integral
of `σ_{0i}` over the face `x_i = b_i` minus that over `x_i = a_i`) equals the
[separate-flow thrust](separate-flow-thrust.md) with inlet flow `ρ_in A₀ v_in,0`, inlet velocity
`v_in,0` (the axial component of `v_in`), inlet pressure `p_in`, exhaust flow `ρ_out A₀ v_out,0`,
exhaust velocity `v_out,0`, exhaust pressure `p_out`, and both port areas equal to
`A₀ = ∏_{j ≠ 0} (b_j − a_j)`.
