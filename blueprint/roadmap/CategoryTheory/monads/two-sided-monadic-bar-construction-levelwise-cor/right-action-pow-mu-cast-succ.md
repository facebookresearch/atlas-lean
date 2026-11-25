# Right Action Pow mu cast Succ

Distant right-endpoint interchange:
`muAtPos` at degree `n+1` and position `castSucc i` commutes with `rightActionPow`.
For `n`, `i : Fin n`, `R.map (muAtPos (n+1) (castSucc i)) ≫ rightActionPow n =
rightActionPow (n+1) ≫ R.map (muAtPos n i)`.
Proved by induction on `n`, using definitional successor equations (`rightActionPow_succ`,
`muAtPos_succ_eq`) with explicit `change` where elaboration does not unfold, and
`rightActionPow_naturality` for the raw position-zero case.
