# High-probability bound on the false discovery proportion

Let `μ` be a probability measure on `Ω` and `(T, G)` a
[tail-calibrated family](is-tail-calibrated-family.md) of `m` tests with true nulls `H0` whose
[p-values](tail-pvalue.md) `p` are positively regression dependent on `H0`, as in
[FDR control](integral-fdp-bh-rejections-tail-pvalue-l.md), and let `0 < q ≤ 1` and `δ > 0`. Then
the event that the Benjamini–Hochberg rejection set `R_q(p)` at level `q` has false discovery
proportion strictly below `q / δ` has probability at least `1 - δ`:
`μ{ω : FDP(H0, R_q(p(ω))) < q / δ} ≥ 1 - δ`, the right side being read as `0` for `δ ≥ 1`. The
statement is informative only for `q ≤ δ < 1`: for `δ < q` the level `q / δ` exceeds `1`, which
the false discovery proportion never exceeds, and for `δ ≥ 1` the bound is trivial. When `H0` is
nonempty, so that `m > 0`, the [Markov bound](measure-le-fdp-bh-rejections-tail-pvalue.md) gives
the sharper level `q |H0| / (m δ)`; when `H0` is empty, the false discovery proportion is `0`.
