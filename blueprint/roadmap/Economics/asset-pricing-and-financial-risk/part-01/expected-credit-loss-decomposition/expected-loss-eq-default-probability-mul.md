# Expected Loss eq default Probability mul conditional Expected Loss

Expected-loss decomposition: expected loss equals the
probability of default times the expected exposure-times-loss-given-default
conditional on default. `ProbabilityTheory.cond μ D` is always defined as the
`(μ D)⁻¹`-scaled restriction, even if `μ D = 0`. The nonzero hypothesis is
required for probability normalization and ordinary conditional-expectation
semantics; for a measurable zero event the conditional measure is zero and
this theorem retains the nonzero hypothesis.
