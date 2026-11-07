# Expected statistics are the design matrix times the parameters

Under the annotation model, the vector of expected statistics is the design matrix applied
to the parameter vector `(σ²_e, τ)` (intercept first). Hence the parameters are determined by
the expected statistics of all markers, whatever their values, iff
`(design X a).rank = Fintype.card (Option ι)` (`injective_mulVec_iff_rank_eq_card`).
