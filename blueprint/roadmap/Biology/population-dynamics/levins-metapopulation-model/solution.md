# Explicit solution of the Levins equation with immigration

For real `c`, `e`, `m` and `p₀`, the explicit solution is
`p(t) = p̂ + L (p₀ - p̂) / ((L + c (p₀ - p̂)) e^{L t} - c (p₀ - p̂))` for real `t`: the
[shifted Riccati trajectory](riccati-traj.md) with `q = p̂`, the
[immigration equilibrium](immigration-eq.md), and `L = c p̂ + m / p̂`, the [return rate](rate.md).

For `c ≥ 0`, `e ≥ 0` and `m > 0` it satisfies `p(0) = p₀`, and for `p₀ ≥ 0` it
[solves the equation for `t ≥ 0`](is-solution-solution.md); its denominator is then at least `L > 0`
for `t ≥ 0`. Outside that range the conventions of the trajectory apply: at `m = 0`, `p̂ = L = 0`
and the formula gives `p(t) = 0` for every `t`, whatever `p₀`.
