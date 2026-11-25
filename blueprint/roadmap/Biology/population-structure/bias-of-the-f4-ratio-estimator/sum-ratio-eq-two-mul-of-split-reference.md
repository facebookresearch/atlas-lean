# Edge-sum f4 ratio with a split reference is twice the proportion

Take two edges with lengths `len = (ℓ, ℓ)`, `ℓ ≠ 0`, weight vectors `wA = wY = (1, 1)`,
`wO = wC = (0, 0)` and `wB = (1, 0)` on them, and `wX = α wY + (1 - α) wC` for a real `α`. Then
`N / D = 2 α`, where `N = ∑ e, (wA e - wO e) * (wX e - wC e) * len e` and
`D = ∑ e, (wA e - wO e) * (wB e - wC e) * len e`. In a
[drift model](../patterson-s-f-statistics/drift-model.md) these sums are the
[f4 statistics](../patterson-s-f-statistics/f4-freq.md) `f4(A, O; X, C)` and `f4(A, O; B, C)`, so
the f4 ratio of a target `X` mixing an unsampled source `Y` with `C`, against a sampled reference
`B` that carries only the first of the two edges of `Y`, is `2 α`. It exceeds `1` when `α > 1/2`, so
the ratio can lie outside `[0, 1]`.
