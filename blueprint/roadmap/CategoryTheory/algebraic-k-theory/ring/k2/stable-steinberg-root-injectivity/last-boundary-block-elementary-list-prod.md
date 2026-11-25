# Last Boundary Block Elementary list prod val

Finite elementary product equals reindexed alternating block product.

Direction is from the finite elementary representatives
`lastBoundaryBlockElementary n` (in `elementarySubgroup (Fin (n+1))`)
to the explicit `GL (Fin n ⊕ Fin 1)` alternating product
`BlockElementary.blockAltProd` reindexed by `finSumFinEquiv`.

Orientation is exact: `Sum.inl c` is column = upper unit
`BlockElementary.upperUnit` with `Matrix.of fun i _ => (c i).toAdd`, and
`Sum.inr r` is row = lower unit `BlockElementary.lowerUnit` with
`Matrix.of fun _ j => (r j).toAdd`.

Generic `[Ring R]` and universe `u`, arbitrary length `L`, empty list gives
`1` via `blockAltProd_nil` and `List.prod` on `[]`, singleton reduces to
`lastBoundaryBlockElementary_inl_val` / `_inr_val`, and `n = 0` is valid
(`Fin 0 → _` is subsingleton, `Fin 1` block is trivial). Multiplication order
preserves head-left `List.prod` (`a :: L` multiplies on the left). This is a
representation/evaluation bridge only; no pivot, scalar equation, alternation,
strict decrease, kernel generation, finite-stage landing, or Matsumoto claim
is made.
