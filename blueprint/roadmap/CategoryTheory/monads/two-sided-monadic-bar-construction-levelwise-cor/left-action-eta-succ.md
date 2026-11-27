# Left Action eta succ

Distant left-endpoint interchange for unit insertion:
`etaAtPos` at degree `n+1` and position `i.succ` commutes with the left action
mapped through `monadPow`. For `n`, `i : Fin (n+1)`, `a`,
`R.map (etaAtPos (n+1) (i.succ)) ≫ R.map (monadPow (n+1) (L.action)) =
R.map (monadPow n (L.action)) ≫ R.map (etaAtPos n i)`.
Thin consequence of `etaAtPos_naturality` at `L.action.app a` and the definitional
successor equation for `etaAtPos`, followed by `R.map`.
