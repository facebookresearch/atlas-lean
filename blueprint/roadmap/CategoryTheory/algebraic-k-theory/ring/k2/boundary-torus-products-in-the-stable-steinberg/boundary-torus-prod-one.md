# Boundary Torus Prod one

Evaluation at rank one: `boundaryTorusProd 1` is the single torus factor.

- Order: `List.ofFn` on `Fin 1 = Fin (0+1)` satisfies `List.ofFn_succ`:
  `ofFn f = f 0 :: ofFn (fun i : Fin 0 => f (Fin.succ i))`. With `List.ofFn_zero` the tail
  is `[]`, so the list is the singleton `[f 0]` and `List.prod [a] = a * 1 = a`
  (`List.prod_cons`, `List.prod_nil`, `mul_one`). The function
  `f` here is `fun i : Fin 1 => torus i.val 1 (Nat.ne_of_lt i.isLt) (u i)`;
  for `i = 0 : Fin 1`, `i.val = 0` definitionally and the inequality proof is
  `Nat.ne_of_lt (0 : Fin 1).isLt : 0 ≠ 1`. Hence the orientation is exactly the
  head-first singleton product induced by `List.ofFn`/`List.prod`.

- Proof closure: after reducing `List.ofFn` on `Fin 1` to the singleton head
  and applying `List.prod_cons`/`List.prod_nil`/`mul_one`, the remaining goal is
  equality of `torus` factors differing only by the `Fin.val` projection and the
  `0 ≠ 1` proof. It is closed by `rfl` giving `hv : (0 : Fin 1).val = 0`
  followed by `simp only [hv]`; the inequality proofs are identified by proof
  irrelevance (subsingleton) and the remaining arguments by `rfl`.

Nonclaims: no general `n+1` successor theorem, no claim that product-one of `u`
forces `boundaryTorusProd = 1`, no kernel claim (`ker toStableE`), and no cocycle
claim; only the exact `n = 1` orientation from the existing definition.
