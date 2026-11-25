# Path coupling tv

Path coupling bound: suppose `Cadj x y` is a one-step coupling
of `K x` and `K y` for every *adjacent* pair `x y`, and the coupled
distance contracts in expectation by `β ≤ 1` on adjacent pairs.
On a finite metric space whose nonzero distances are at least
`δ > 0`, and where every two points are joined by a `Path` (adjacent
steps with additive distance), the chains started at `x`, `y`
satisfy `tvDist ≤ β^t * dist x y / δ` after `t` steps. The
all-pairs coupling is obtained by gluing the adjacent couplings
along the path, then iterating it.
