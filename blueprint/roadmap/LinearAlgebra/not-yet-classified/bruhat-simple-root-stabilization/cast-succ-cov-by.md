# Cast Succ cov By

`Fin.castSucc` preserves `CovBy` / adjacency.

For `Fin n` the order is `i < j ↔ i.val < j.val`; `i ⋖ j` means
`j.val = i.val + 1`. The map `castSucc : Fin n → Fin (n+1)` has
`(castSucc i).val = i.val` and is strictly monotone, so it preserves
covers. This is the small order lemma needed for simple-root
stabilization.
