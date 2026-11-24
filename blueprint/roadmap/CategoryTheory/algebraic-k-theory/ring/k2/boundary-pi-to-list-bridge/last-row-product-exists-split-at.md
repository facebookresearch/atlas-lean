# Last Row Product exists split at

For generic `[Ring R]`, `lastRowProduct` at `k : Fin n` splits the
increasing `List.ofFn` product into `A` before `k`, the singleton
`x n k.val (Ne.symm (Nat.ne_of_lt k.isLt)) (r k).toAdd`, and `C` after `k`.
Uses `Ne.symm (Nat.ne_of_lt k.isLt)` for the root witness and pinned
`List.take` / `List.drop` / `List.getElem` to preserve `0, ..., n-1` order.
Equality in `StableSteinberg R` only, not a finite-stage, kernel, collection,
landing, minimal-normal-form, or Matsumoto result.
