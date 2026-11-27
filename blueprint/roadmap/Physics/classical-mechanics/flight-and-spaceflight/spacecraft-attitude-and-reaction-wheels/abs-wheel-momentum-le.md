# A momentum reserve bounds the wheel momentum at all later times

Let `I > 0`, `k > 0` and `ω₀`, `h₀`, `h_max` be real numbers with `|h₀| + I |ω₀| ≤ h_max`, which
forces `h_max ≥ 0`. Then the [wheel momentum](wheel-momentum.md)
`h_w(t) = h₀ + I ω₀ (1 − exp(−k t / I))` obeys `|h_w(t)| ≤ h_max` at every `t ≥ 0`. No relation
between `ω₀` and the command limit is needed.
