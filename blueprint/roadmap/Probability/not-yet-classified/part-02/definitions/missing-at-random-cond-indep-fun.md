# Missing at random

**Missing at random** (Rubin 1976): the response indicator `ω ↦ ω ∈ R` is conditionally
independent of the outcome `Y` given the always-observed covariate `X`, as Mathlib's
`CondIndepFun` given the σ-algebra `σ(X)`. The measurability proof `hX` only certifies
`σ(X) ≤ mΩ`. The discrete-covariate form used by the AIPW development is
`MathlibExt.Probability.Causality.MissingOutcomes.MissingAtRandom`; the two agree on their
common domain (`missingAtRandomCondIndepFun_iff_missingAtRandom`).
