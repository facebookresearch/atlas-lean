# Portfolio beta is linear in portfolio weights (FI07.T01)

When the market
variance is positive, the beta of the portfolio return `∑ i, w i * R i ω` is the
weight-weighted sum of the asset betas. The proof is covariance additivity /
homogeneity in the first slot (`covariance_fun_sum_left`,
`covariance_const_mul_left`) plus `Finset.sum_div`; the cited Mathlib lemmas
are not reproved. The hypothesis `hVar` is contract-required (with the
probability-measure and `MemLp` hypotheses, it is what makes each ratio a CAPM
beta) even though the field identity holds without it.
