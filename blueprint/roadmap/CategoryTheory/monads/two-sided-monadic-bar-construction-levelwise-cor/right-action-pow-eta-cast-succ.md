# Right Action Pow eta cast Succ

Distant right-endpoint unit insertion:
`etaAtPos` at degree `n+1` and position `castSucc i` commutes with `rightActionPow`.
For `n`, `i : Fin (n+1)`,
`R.map (etaAtPos (n+1) (castSucc i)) ≫ rightActionPow (n+1) = rightActionPow n ≫
R.map (etaAtPos n i)`.
Proved by induction on `n`, using definitional successor equations (`rightActionPow_succ`,
`etaAtPos_succ_eq`) with explicit `change` where elaboration does not unfold, and
`RightModule.action.naturality` in the base case and `rightActionPow_naturality` for the raw
position-zero case.
