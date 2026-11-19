/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.HermitianDilation
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.HermitianDilation

namespace MathlibExtTest.LinearAlgebra.Matrix.HermitianDilation

/-- The dilation of a `2 × 3` complex matrix is a Hermitian `5 × 5` (block) matrix. -/
example (B : Matrix (Fin 2) (Fin 3) ℂ) : (dilation B).IsHermitian := isHermitian_dilation B

/-- The square of the dilation of a row vector `[1, 0]` has the blocks `B Bᴴ = [1]` and
`Bᴴ B = diag(1, 0)`. -/
example : dilation (!![1, 0] : Matrix (Fin 1) (Fin 2) ℂ) * dilation !![1, 0] =
    fromBlocks !![1] 0 0 !![1, 0; 0, 0] := by
  rw [dilation_mul_self]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- Real scalars pass through the dilation of a complex matrix. -/
example (r : ℝ) (B : Matrix (Fin 2) (Fin 2) ℂ) : dilation (r • B) = r • dilation B :=
  dilation_smul r B

end MathlibExtTest.LinearAlgebra.Matrix.HermitianDilation
