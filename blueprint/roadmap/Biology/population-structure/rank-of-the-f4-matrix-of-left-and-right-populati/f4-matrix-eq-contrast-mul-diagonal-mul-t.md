# Drift-model factorization of the f4 matrix through weight contrasts

In every [drift model](../patterson-s-f-statistics/drift-model.md) on a measure `μ`, with lineage
weights `w` and drift lengths `ℓ`, and for left populations `L 0, …, L n` and right populations
`R 0, …, R r`, the [qpWave matrix](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) `F` of
the [population frequencies](../patterson-s-f-statistics/freq.md) factors as `F = C_L diag(ℓ) C_Rᵀ`,
where `C_L` and `C_R` are the [contrast matrices](contrast-matrix.md) of `L` and `R`. Entrywise,
`f4(L i, L 0; R j, R 0) = ∑ e, (w (L i) e - w (L 0) e) * ℓ e * (w (R j) e - w (R 0) e)` for
`1 ≤ i ≤ n` and `1 ≤ j ≤ r`.
