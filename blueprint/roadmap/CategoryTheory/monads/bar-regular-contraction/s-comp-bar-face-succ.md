# S comp bar Face succ

Regular-right positive-face contraction law.

For `n : ℕ` and `i : Fin (n+2)`, `i.succ : Fin (n+3)` is the positive
face at level `n+1`.  `s L (n+1)` inserts `η` at `B_{n+1}` then
`eqToHom (barObj_obj_succ_eq (n+1))⁻¹`.  Using `T.η.naturality`,
the comparison reduces to the transport-aware face coherence
`eq⁻¹ ≫ d_{i.succ} = T(d_i) ≫ eq⁻¹`, i.e. forward
`d_{i.succ} ≫ eq = eq ≫ T(d_i)`.

We split `i : Fin (n+2)` into endpoint vs interior:

* endpoint `i = last (n+1)` (`i.val = n+1`): `d_{last}` is the left
  action `T.map (M_n.map L.action)`.  Forward coherence is
  `monadPow_obj_T_comm_naturality T n (L.action)` together with
  `eqToHom_map`.

* interior `i.val ≤ n`: further into `i.val = 0` (right action) and
  `1 ≤ i.val ≤ n` (μ).  For `i=0`, `d_0 = rightActionPow n` and
  `d_1 = T.map (muAtPos (n+1) (last n))`; forward coherence is
  `mu_last_coherence`.  For `1 ≤ i ≤ n`, write `i = ⟨k+1⟩` with
  `k : Fin n`, `k' = k.succ : Fin (n+1)`, then
  `barMuAtPos n k = muAtPos n k.rev`, `barMuAtPos (n+1) k' = muAtPos (n+1) (k.rev).castSucc`,
  and `fin_rev_succ` gives the `castSucc` position.  Forward coherence
  is `mu_castSucc_coherence`.

In each case the forward equality `d_{i.succ} ≫ eq(b_n) = eq(b_{n+1}) ≫ T(d_i)`
is transformed to the inverse form `eq(b_{n+1})⁻¹ ≫ d_{i.succ} = T(d_i) ≫ eq(b_n)⁻¹`
via `eqToHom_comp_symm_eq` / `eqToHom_symm_comp_eq` and `Category.assoc`,
exactly as in `s_comp_barFace_zero`.  Finally `T.η.naturality` rewrites
`η_{n+1} ≫ T(d_i)` to `d_i ≫ η_n`, yielding the claimed
`s_{n+1} ≫ d_{i.succ} = d_i ≫ s_n`.
