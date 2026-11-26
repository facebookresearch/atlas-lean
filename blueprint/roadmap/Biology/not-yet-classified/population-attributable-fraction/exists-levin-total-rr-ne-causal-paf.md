# Levin's formula with an adjusted risk ratio can disagree with the PAF

There is a
nondegenerate confounded finite strata model with two strata, `P(z) > 0`, `∑_z P(z) = 1`,
`0 < e(z) < 1`, strictly positive risks `0 < r₀(z), r₁(z) ≤ 1` (hence positive observed and
counterfactual risks), and confounding (`e 0 ≠ e 1` and `r₀ 0 ≠ r₀ 1`), in which Levin's formula
with `Pe` and the risk ratio standardized to the total population differs from the causal
attributable fraction (Khosravi et al. 2021). This is a counterexample: it shows that the two can
disagree in one confounded model, not that they disagree in every confounded model, and it is not
a statement about the bias of an estimator.

## Sources

- Khosravi et al. (2021), who call Levin's formula "biased in the presence of confounding even if the adjusted RR is used"; the counterexample is derived.
