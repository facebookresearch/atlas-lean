# Rank deficiency implies non-identifiability

If `m < n`, the linear map
`A.mulVecLin : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)` has a nontrivial kernel by
`LinearMap.ker_ne_bot_of_finrank_lt` (rank-nullity: `finrank` of source `n` exceeds
`finrank` of target `m`, via `Module.finrank_fin_fun`), and any nonzero kernel
vector defeats injectivity.
