# Markov bound on the false discovery proportion

Let `μ` be a probability measure on `Ω` and `(T, G)` a
[tail-calibrated family](is-tail-calibrated-family.md) of `m` tests with true nulls `H0` whose
[p-values](tail-pvalue.md) `p` are positively regression dependent on `H0`, as in
[FDR control](integral-fdp-bh-rejections-tail-pvalue-l.md), and let `0 ≤ q ≤ 1` and `c > 0`. Then
the probability that the Benjamini–Hochberg rejection set `R_q(p)` at level `q` has false discovery
proportion at least `c` is at most `q |H0| / (m c)`:
`μ{ω : c ≤ FDP(H0, R_q(p(ω)))} ≤ q |H0| / (m c)`, a bound that is `0` for `m = 0` by the convention
`x / 0 = 0`. It follows from the false discovery rate bound by Markov's inequality.
