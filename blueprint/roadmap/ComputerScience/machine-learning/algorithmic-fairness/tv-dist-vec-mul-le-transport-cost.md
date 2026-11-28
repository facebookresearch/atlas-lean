# Classifier-level transport bound

Let `M` be a classifier on a finite outcome set that
is individually fair with respect to a task metric `d`, `S T : V → ℝ` weight vectors on a
finite set of individuals, not necessarily probability distributions, and `π` a coupling of
them (nonnegative entries, row sums `S`, column sums `T`). Then the total variation distance
between the outcome vectors `S ᵥ* Matrix.of M` and `T ᵥ* Matrix.of M`, with entries
`∑ x, S x * M x o` and `∑ x, T x * M x o`, is at most `transportCost d π`, the cost of `π` for
the same `d`.
