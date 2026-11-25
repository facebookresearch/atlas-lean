# Left Action mu succ

Distant left-endpoint interchange for multiplication:
`muAtPos` at degree `n+1` and position `i.succ` commutes with the left action
mapped through `monadPow`. For `n`, `i : Fin n`, `a`,
`R.map (muAtPos (n+1) (i.succ)) ≫ R.map (monadPow n (L.action)) =
R.map (monadPow (n+1) (L.action)) ≫ R.map (muAtPos n i)`.
Thin consequence of `muAtPos_naturality` at `L.action.app a` and the definitional
successor equation for `muAtPos`, followed by `R.map`.
