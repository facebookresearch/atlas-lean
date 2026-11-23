# FDR control for independent tail-calibrated tests

Let `μ` be a probability measure on `Ω` and `(T, G)` a
[tail-calibrated family](is-tail-calibrated-family.md) of `m` tests with true nulls `H0`, whose
statistics `T 0, …, T (m - 1)` are mutually independent under `μ`. Then for every level
`0 ≤ q ≤ 1` the
[Benjamini–Hochberg rejection set](bh-rejections.md)
`R_q(p)` of the [p-values](tail-pvalue.md) `p = (G i ∘ T i)_i` has false discovery rate at most
`q |H0| / m`: `∫ FDP(H0, R_q(p(ω))) dμ(ω) ≤ q |H0| / m`, with the
[false discovery proportion](../valid-p-values-and-false-discovery-proportion/false-discovery-proportion.md)
`FDP(H0, R) = |R ∩ H0| / max(|R|, 1)`; for `m = 0` the bound is `0` by the convention `x / 0 = 0`.
This is a special case of
[FDR control under positive regression dependence](integral-fdp-bh-rejections-tail-pvalue-l.md),
as independent statistics give
[positively regression dependent p-values](is-prdson-tail-pvalue-of-i-indep-fun.md).
