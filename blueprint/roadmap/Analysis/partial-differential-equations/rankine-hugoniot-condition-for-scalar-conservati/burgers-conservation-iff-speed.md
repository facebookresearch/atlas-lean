# A Burgers jump conserves mass exactly at the mean speed

For constant states `u_L ≠ u_R`, an interface `s : ℝ → ℝ` with derivative `c` at time `t`, and
`a < s(t) < b`, the split mass `τ ↦ ∫_a^{s(τ)} u_L dx + ∫_{s(τ)}^b u_R dx` has derivative
`f(u_L) - f(u_R)` at `t`, for the [Burgers flux](burgers-flux.md) `f`, if and only if
`c = (u_L + u_R) / 2`.
