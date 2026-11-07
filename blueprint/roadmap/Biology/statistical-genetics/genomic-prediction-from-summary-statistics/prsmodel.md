# Effect-estimate model for polygenic score accuracy

The effect-estimate model behind polygenic-score accuracy (Daetwyler et al. 2008;
Dudbridge 2013), at the level of raw second moments, for `M` independent markers: true effects
`beta k` with `∫ β k β l = (h² / M) [k = l]`, estimation errors `err k` with
`∫ e k e l = s² [k = l]`, orthogonal to the effects. The estimates are `β̂ = β + e`
(`betaHat`). For a probability measure and mean-zero effects and errors these are the
covariance conditions of the cited model; `s²` is the sampling variance of each estimate
(`1 / N` in the cited papers, `(1 - h²) / N` in `ofLDScore`).
