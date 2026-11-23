# FDR control for tail-calibrated rare-variant tests

Let `μ` be a probability measure on `Ω` and `(T, G)` a
[tail-calibrated family](is-tail-calibrated-family.md) of `m` tests with true nulls `H0`, whose
[p-values](tail-pvalue.md) `p = (G i ∘ T i)_i` are positively regression dependent on `H0`: for
every `i ∈ H0` and every measurable set `D ⊆ ℝ^m` closed under increasing coordinates,
`x ↦ μ(p ∈ D | p_i = x)` has a nondecreasing version. Then for every level `0 ≤ q ≤ 1` the
[Benjamini–Hochberg rejection set](bh-rejections.md)
`R_q(p)` has false discovery rate at most `q |H0| / m`:
`∫ FDP(H0, R_q(p(ω))) dμ(ω) ≤ q |H0| / m`, where `FDP(H0, R) = |R ∩ H0| / max(|R|, 1)` is the
[false discovery proportion](../valid-p-values-and-false-discovery-proportion/false-discovery-proportion.md),
`0` when nothing is rejected. For `m = 0` the bound is `0` by the convention `x / 0 = 0`.

## Sources

- Benjamini & Yekutieli (2001), Theorem 1.2.
