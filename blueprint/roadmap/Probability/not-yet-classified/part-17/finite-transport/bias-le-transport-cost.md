# Score-gap bound for one coupling

Let `S T : V → ℝ` be weight vectors on a finite
type, not necessarily probability distributions, and `π` a coupling of them (nonnegative
entries, row sums `S`, column sums `T`). For a score `f : V → ℝ` with
`|f x - f y| ≤ d x y` for all `x, y`, the gap
`bias S T f = |∑ x, S x * f x - ∑ x, T x * f x|` is at most `transportCost d π`.
