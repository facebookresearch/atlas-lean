# For D ≠ 0, the forced response is the unique C² solution with its data

Let `m > 0`, `c ≥ 0` and `k > 0`, let `F` and `Ω` be real numbers with nonzero
[steady-state denominator](steady-state-denominator.md), and let `x₀` and `v₀` be real numbers. If
`x : ℝ → ℝ` is twice continuously differentiable, satisfies
`m x''(t) + c x'(t) + k x(t) = F cos (Ω t)` at every time `t`, and has `x(0) = x₀` and
`x'(0) = v₀`, then `x` is the [forced response](forced-response.md) with initial data `x₀`, `v₀`.
The forced response is itself such a solution ([solution and initial data](forced-response-spec.md)),
so it is the only one.
