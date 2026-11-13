# Certificate of global optimality

If `g` supports `f` at `x` on `S` and `g` is
nonnegative on every feasible direction `y - x` (`y ∈ S`), then `x` minimizes `f` on `S`. For a
feasible candidate `x ∈ S` this says `x` is a global minimizer on `S`; the inequality does not
need membership, and, as in Mathlib's `IsMinOn`, membership is not part of the conclusion.
