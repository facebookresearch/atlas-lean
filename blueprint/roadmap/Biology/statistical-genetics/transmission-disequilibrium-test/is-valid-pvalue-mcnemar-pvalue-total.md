# McNemar's test under the equal-rate Poisson null

Let the discordant counts `X ~ Po(r)`
and `Y ~ Po(r)` be independent with a common rate `r ≥ 0` (the Poissonized null of marginal
homogeneity). Then the McNemar p-value at the observed number of discordant pairs,
`ω ↦ P(Bin(X ω + Y ω, 1/2) ≥ X ω)`, is valid under `μ`, whatever `r`. The same statement is the
TDT when `X` and `Y` are the transmitted and untransmitted counts *modeled* as independent
Poisson counts with equal rates; that is a statistical model of the counts, not a consequence of
Mendelian segregation. This is the merged `GLM.CountData.isValidPValue_countExactPValue` with
library sizes `s₁ = s₂ = 1`, restated for `mcnemarPValue`.
