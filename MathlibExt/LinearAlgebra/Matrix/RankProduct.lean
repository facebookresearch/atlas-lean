/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Rank of a matrix product -/

public section

namespace Matrix

/-- **Rank of a product of matrices.** For matrices $A$ of size $m \times r$ and
$B$ of size $r \times n$ over a field, the rank of $AB$ is at most the
minimum of the ranks of $A$ and $B$, and that minimum is at most $r$.

The first inequality is Mathlib's `Matrix.rank_mul_le`; for the second,
the rank of $A$ is at most its number of columns.

See Axler, *Linear Algebra Done Right*, 4th ed., §3B, Exercise 23, for the
corresponding bound on the dimension of the range of a composition. -/
theorem rank_mul_le_min_and_min_le_width {K : Type*} [Field K] {m r n : ℕ}
    (A : Matrix (Fin m) (Fin r) K) (B : Matrix (Fin r) (Fin n) K) :
    (A * B).rank ≤ min A.rank B.rank ∧ min A.rank B.rank ≤ r :=
  ⟨rank_mul_le A B, (min_le_left _ _).trans (rank_le_width A)⟩

end Matrix
