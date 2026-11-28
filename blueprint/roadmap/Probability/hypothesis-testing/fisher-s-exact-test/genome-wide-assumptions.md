# Hypotheses on p-values for a genome-wide multiple-testing step

Let `μ` be a probability measure on `Ω`, `p = (p 0, …, p (m - 1))` the real p-values of `m`
variants, `H0 ⊆ {0, …, m - 1}` the unknown set of true nulls and `r` a
[dependence regime](dependence-regime.md). The genome-wide assumptions hold when every `p i` is
measurable, every `p i` with `i ∈ H0` is a
[valid p-value](../valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)
under `μ` (`μ{p i ≤ s} ≤ s` for every `s ∈ [0, 1]`), and `p` satisfies the
[hypothesis of the regime](holds.md) `r`. These are the hypotheses under which a
Benjamini–Hochberg or Benjamini–Yekutieli step is applied. They are assumptions, not consequences:
validity is supplied variant by variant (for the allelic test,
[under its binomial null](is-valid-pvalue-allelic-pvalue.md)), and the dependence hypothesis must
be justified separately for the variants at hand.
