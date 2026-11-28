# Exponential bound on a diagonal's exceedance probability

Let `p` and `q` be
[probability vectors](../../../../Probability/not-yet-classified/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters and `θ ≥ 0` a root of
`∑_{a, b} p_a q_b e^{θ s(a, b)} = 1` ([pair law](pair-law.md), [pair score](pair-score.md)). Then
for all natural numbers `m` and `n`, every `t > 0` and every integer `d`, the
[exceedance probability](exceed-prob.md) satisfies `p_d ≤ L e^{-θ t}`, where
`L = min(m - (-d)⁺, n - d⁺)` is the [diagonal length](diag-len.md). For `θ = 0` the bound is `L`.
