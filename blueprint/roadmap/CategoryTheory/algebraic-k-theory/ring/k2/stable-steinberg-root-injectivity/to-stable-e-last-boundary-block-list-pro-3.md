# To Stable E last Boundary Block list prod eq one imp block Alt Prod eq one

From a stable-trivial boundary word to a trivial alternating block product.

If the `toStableE`-image of the `lastBoundaryBlock n` word
`(L.map lastBoundaryBlock n).prod` is `1` in `StableE`, then the explicit
alternating block product in `GL (Fin n ⊕ Fin 1)` is `1`.

Direction uses the finite elementary-product equality
`toStableE_lastBoundaryBlock_list_prod_eq_one_imp` to obtain
`((L.map lastBoundaryBlockElementary n).prod : elementarySubgroup) = 1`,
coerces to `GL (Fin (n+1))`, rewrites via
`lastBoundaryBlockElementary_list_prod_val`, and applies injectivity of
`reindexMulEquiv (finSumFinEquiv)`.

Orientation is exact: `Sum.inl` is column = upper unit with
`Matrix.of fun i _ => (c i).toAdd`, `Sum.inr` is row = lower unit with
`Matrix.of fun _ j => (r j).toAdd`.

Generic `[Ring R]` and universe `u`, arbitrary `L`, empty `L` gives `1` on
both sides, singleton reduces to the single-block evaluation, and `n = 0`
is valid (`Fin 0` vectors are trivial). This is a representation/evaluation
bridge only; no pivot, scalar equation, alternation, strict decrease, kernel
generation, finite-stage landing, Weyl stage drop, torus-cocycle, or
Matsumoto claim is made.
