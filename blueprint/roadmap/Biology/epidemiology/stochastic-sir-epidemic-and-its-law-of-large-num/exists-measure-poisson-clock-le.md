# Uniform law of large numbers for a unit Poisson clock

**Uniform law of large numbers for a unit Poisson clock**, with an explicit Chebyshev
rate: for every `B` and `η > 0` there is `C` such that, for every unit-rate Poisson process `Y`
and every `N ≥ 1`, `sup_{a ∈ [0, B]} |Y(N a) / N - a| > η` has probability at most `C / N`.

Proof: on the grid `a_k = k η / 4` (`k ≤ ⌈4 B / η⌉ + 1`) Chebyshev bounds each
`|Y(N a_k) / N - a_k| ≥ η / 2`; off the union of these events (and the null event where `Y` is
not a nondecreasing path from `0`) monotonicity of `Y` squeezes `Y(N a) / N` between two
consecutive grid values, which keeps it within `3 η / 4` of `a`.
