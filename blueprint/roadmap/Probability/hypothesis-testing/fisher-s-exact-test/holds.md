# Hypothesis imposed by a dependence regime

Let `μ` be a finite nonzero measure on `Ω`, `p = (p 0, …, p (m - 1))` a vector of real p-values on
`Ω` and `H0` a subset of `{0, …, m - 1}`, the true nulls. The hypothesis that a
[dependence regime](dependence-regime.md) imposes on `p` is:

- for the independent regime, that `p 0, …, p (m - 1)` are mutually independent under `μ`, which
  forces `μ` to be a probability measure;
- for the PRDS regime, that `p` is positively regression dependent on `H0`: for every `i ∈ H0` and
  every measurable set `D ⊆ ℝ^m` closed under increasing coordinates, the conditional
  probability `x ↦ μ(p ∈ D | p i = x)`, a regular conditional distribution determined up to null
  sets of the law of `p i`, has a nondecreasing version (for p-values that are not almost
  everywhere measurable this condition does not describe their laws);
- for the arbitrary regime, nothing: the hypothesis always holds.
