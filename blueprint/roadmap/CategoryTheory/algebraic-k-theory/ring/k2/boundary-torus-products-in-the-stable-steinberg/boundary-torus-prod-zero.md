# Boundary Torus Prod zero

Evaluation at rank zero: `boundaryTorusProd 0` is the empty product.

- Order: `boundaryTorusProd` is defined as
  `(List.ofFn (fun i : Fin n => torus i.val n _ (u i))).prod`.
  `List.ofFn` enumerates `Fin n` in increasing order `0,1,…,n-1`. `List.prod` multiplies
  as `a₀ * (a₁ * (⋯ * 1))`. At `n = 0`, `List.ofFn` on `Fin 0` is `[]` (`List.ofFn_zero`),
  and `List.prod [] = 1` (`List.prod_nil`). So the orientation is the empty product.

Nonclaims: this lemma makes no claim about a general `(n+1)` successor decomposition,
no claim that `∏ u = 1` implies `boundaryTorusProd = 1`, no kernel-membership claim,
and no cocycle-identity claim. Only the `n = 0` evaluation with the exact
`List.ofFn`/`List.prod` orientation.
