# A compact Lyapunov sublevel set between two balls

For the [quadratic Lyapunov function](longitudinal-lyapunov.md) `V` on the state
`e = (x, z, θ, q) ∈ ℝ⁴` with the Euclidean norm:

- the sublevel set `{V ≤ 1/80000}` is compact;
- it contains every state with `‖e‖ ≤ 1/400`, since `V ≤ 2 ‖e‖²`;
- every state in it has `‖e‖² ≤ 1/20000`, since `V ≥ ‖e‖² / 4`, and its coordinates lie in the
  [actuator box](actuator-box.md).

With `r = 1/100`, these are the sublevel set `{V ≤ r² / 8}`, the ball of radius `r / 4` and the
ball of radius `r / √2`.
