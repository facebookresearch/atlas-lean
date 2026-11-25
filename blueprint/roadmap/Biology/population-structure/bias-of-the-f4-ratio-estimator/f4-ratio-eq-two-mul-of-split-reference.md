# The f4 ratio with a split reference is twice the admixture proportion

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) with two edges, both of drift
length `ℓ ≠ 0`, and populations `A, O, X, Y, B, C` whose lineage weight vectors on the two edges are
`w A = w Y = (1, 1)`, `w O = w C = (0, 0)`, `w B = (1, 0)` and `w X = α w Y + (1 - α) w C` for a
real `α`. Then the ratio of [f4 statistics](../patterson-s-f-statistics/f4.md) of the
[population frequencies](../patterson-s-f-statistics/freq.md) is
`f4(A, O; X, C) / f4(A, O; B, C) = 2 α`. The sampled reference `B` carries only the first of the two
edges of the unsampled source `Y`, and the ratio exceeds `1` when `α > 1/2`. The computation on the
edge sums alone is the [real-number form](sum-ratio-eq-two-mul-of-split-reference.md).
