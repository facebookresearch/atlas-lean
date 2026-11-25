# Torus mem normalizer finite Stage

Arbitrary-index torus normalizer membership.

For any `i < n` and `u : Fˣ`, the torus `torus i n u` lies in the normalizer of
`finiteStage n`. Uses `torus_eq_zero_last_mul_finiteStage` to write
`torus i n u = torus 0 n u * f` with `f ∈ finiteStage n`, the common-base
`torus_zero_last_mem_normalizer_finiteStage` at `0 < n` for the `torus 0 n`
factor (up to proof irrelevance for the `0 ≠ n` witness), `Subgroup.le_normalizer`
for the `finiteStage` factor, and closure of the normalizer subgroup under
multiplication. Generic in the existing field section; valid for all `i < n`
including `i = 0`. No claim of membership in `finiteStage n`, centrality,
absorption, kernel generation, or Matsumoto.
