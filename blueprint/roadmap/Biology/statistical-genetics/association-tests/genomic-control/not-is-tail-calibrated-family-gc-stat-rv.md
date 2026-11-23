# The calibration assumption is impossible under the global null, for every `m`

If the
scores are almost surely not all zero, the estimated-`λ̂` family is never tail-calibrated against
`χ²₁` on the set of all genes: calibration would give `E[T_j] < 1` for every `j`
(`lintegral_gcStatRV_lt_one`), hence `E[∑ⱼ T_j] < m`, while `∑ⱼ T_j = m` almost surely.
No Gaussianity, independence or other assumption on the law of the scores is used. So the
assumption can hold only when some genes are non-null and inflate `λ̂`.
