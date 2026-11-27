/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.CholeskyNoGrowth
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.CholeskyNoGrowth

namespace MathlibExtTest.LinearAlgebra.Matrix.CholeskyNoGrowth

/-- `L = [[1, 0], [1, 1]]` gives `A = L Lᵀ = [[1, 1], [1, 2]]`; the off-diagonal entry of
`|L| |Lᵀ|` is `1 ≤ √1 √2`, and every entry is at most `max Aₖₖ = 2`. -/
example : ∑ k, |(!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) 0 k| *
      |(!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) 1 k| ≤ 2 :=
  sum_abs_mul_abs_le_of_diag_le !![1, 0; 1, 1] !![1, 1; 1, 2]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; norm_num)
    (by intro k; fin_cases k <;> norm_num) 0 1

end MathlibExtTest.LinearAlgebra.Matrix.CholeskyNoGrowth
