# Torus inv mem finite Stage succ

For `[Field F]`, `hi : i < n`, `u : Fˣ`, the inverse
`(torus (R := F) i n _ u)⁻¹` lies in `finiteStage (R := F) (n + 1)`.
The `n + 1` bound is inherited from `torus_mem_finiteStage_succ`; the
statement is vacuous at `n = 0` and uses only subgroup inverse closure,
not torus multiplicativity or any new root wrapper.
