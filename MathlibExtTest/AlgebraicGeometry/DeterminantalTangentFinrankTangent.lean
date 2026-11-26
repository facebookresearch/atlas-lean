/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DeterminantalTangentFinrankTangent

/-!
# Tests for determinantal tangent dimensions

These tests apply the dimension theorem at a zero matrix and a rank-one diagonal matrix,
and specialize it to rank-one rectangular matrices.
-/

namespace MathlibExtTest.AlgebraicGeometry.DeterminantalTangentFinrankTangent

open MathlibExt.AlgebraicGeometry.DeterminantalTangent
open WantedExt.AlgebraicGeometry.DeterminantalTangentWanted

example {k : Type*} [Field k] :
    Module.finrank k (tangent 0 (0 : Matrix (Fin 2) (Fin 3) k)) = 0 := by
  simpa using finrank_tangent (r := 0) (0 : Matrix (Fin 2) (Fin 3) k)
    (by simp) (by decide) (by decide)

example : Module.finrank ℚ (tangent 1 (Matrix.diagonal ![(1 : ℚ), 0])) = 3 := by
  exact finrank_tangent (Matrix.diagonal ![(1 : ℚ), 0])
    (by rw [Matrix.rank_diagonal]; decide) (by decide) (by decide)

example {k : Type*} [Field k] (A : Matrix (Fin 2) (Fin 3) k) (hA : A.rank = 1) :
    Module.finrank k (tangent 1 A) = 4 :=
  finrank_tangent A hA (by decide) (by decide)

end MathlibExtTest.AlgebraicGeometry.DeterminantalTangentFinrankTangent
