# For c > 0, e < c and p₀ > 0, the distance to p* decays exponentially

**Exponential convergence.** For real numbers `c > 0` and `e < c`, an initial value `p₀ > 0` and a
time `t ≥ 0`, the [explicit solution](levins.md) `p` with `p(0) = p₀` satisfies
`|p(t) - p*| ≤ (p* / min(p₀, p*)) |p₀ - p*| e^{-(c - e) t}`, where `p* = 1 - e / c > 0` is the
[persistence equilibrium](persistence-eq.md). So `p(t)` tends to `p*` at least at the exponential
rate `c - e`.
