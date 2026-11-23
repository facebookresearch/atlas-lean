# Sum ratio eq two mul of split reference

A split-reference f4 ratio that can lie outside `[0, 1]`. Two edges of the same nonzero
drift length `ℓ`, with lineage weights `wA = (1, 1)`, `wO = wC = (0, 0)`,
unsampled source `wY = (1, 1)`, sampled reference `wB = (1, 0)` (weight only
on the first of the two edges carrying `wY`), and admixed target
`wX = α wY + (1 - α) wC`. In
the drift-model form `f4(P, Q; R, S) = ∑ e, (wP e - wQ e) * (wR e - wS e) * len e`,
the ratio `f4(A, O; X, C) / f4(A, O; B, C)` equals `2 * α`, which exceeds `1`
when `α > 1 / 2`.
