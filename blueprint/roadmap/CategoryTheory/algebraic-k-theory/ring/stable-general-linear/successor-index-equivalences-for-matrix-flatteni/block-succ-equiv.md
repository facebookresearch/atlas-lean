# Block Succ Equiv

Block-indexed successor equivalence
`(Fin n × ι) ⊕ (Fin 1 × ι) ≃ Fin ((n+1) * card ι)`.

Successor-index `n` adds a trailing `card ι` block; flattening orients outer
`Fin n` slowest (`finProdMatrixEquiv_val`) and `ι` via noncanonical
`equivFinMatrix`. Built as `(finProdMatrixEquiv n ⊕ (finProdMatrixEquiv 1 ≫
oneMulFinCongr)) ≫ finSumFinEquiv ≫ castSuccMul`.
