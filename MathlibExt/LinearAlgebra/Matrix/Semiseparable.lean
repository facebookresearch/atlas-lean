/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Lower-triangular semiseparable matrices
-/

namespace MetaMathlibExt.Matrix

/-- **Semiseparable matrix.** A lower-triangular $T \times T$ matrix $M$ over a field is
$N$-semiseparable if every submatrix contained in its lower triangle, including the diagonal,
has rank at most $N$. Equivalently, for each index $s$, the block with rows at least $s$ and
columns at most $s$ has rank at most $N$.

Source: Tri Dao and Albert Gu, *Transformers are SSMs: Generalized Models and Efficient
Algorithms Through Structured State Space Duality*, arXiv:2405.21060 (v1), Definition 3.1. -/
@[expose] public def IsSemiseparable {K : Type*} [Field K] {T : ℕ}
    (M : Matrix (Fin T) (Fin T) K) (N : ℕ) : Prop :=
  M.IsLowerTriangular ∧
    ∀ s : Fin T,
      (M.submatrix (Subtype.val : Set.Ici s → Fin T) (Subtype.val : Set.Iic s → Fin T)).rank ≤ N

end MetaMathlibExt.Matrix
