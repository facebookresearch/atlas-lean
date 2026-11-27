/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul

/-! # Tests for `MathlibExt.NumberTheory.GeneralizedMarkovUniquenessMulEMul` -/

namespace MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessMulEMul

open MetaMathlibExt

-- The matrix `!![0, 1; -1, 3]` is a `0`-generalized Cohn matrix: it has determinant `1`,
-- upper-right entry `1` (a `0`-generalized Markov number via `(1, 1, 1)`), and trace `3`.
example : IsGenCohnMatrix 0 !![0, 1; -1, 3] := by
  unfold IsGenCohnMatrix IsGenMarkovNumber
  exact ⟨by decide, 1, rfl, ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩, by decide⟩

-- The first identity on the concrete `0`-generalized Cohn matrix `!![0, 1; -1, 3]`.
example : (!![0, 1; -1, 3] * !![0, 0; 3, 0] * !![0, 1; -1, 3] :
    Matrix (Fin 2) (Fin 2) ℤ)
    = (3 : ℤ) • !![0, 1; -1, 3] + !![0, 0; 3, 0] := by
  have hM : IsGenCohnMatrix 0 !![0, 1; -1, 3] := by
    unfold IsGenCohnMatrix IsGenMarkovNumber
    exact ⟨by decide, 1, rfl, ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩, by decide⟩
  exact (IsGenCohnMatrix.mul_E_mul hM).1

-- The second identity on the same matrix, with the inverse kept symbolic.
example : (!![0, 1; -1, 3]⁻¹ * !![0, 0; 3, 0] * !![0, 1; -1, 3]⁻¹ :
    Matrix (Fin 2) (Fin 2) ℤ)
    = (-((!![0, 1; -1, 3]⁻¹).trace + 0)) • !![0, 1; -1, 3]⁻¹ + !![0, 0; 3, 0] := by
  have hM : IsGenCohnMatrix 0 !![0, 1; -1, 3] := by
    unfold IsGenCohnMatrix IsGenMarkovNumber
    exact ⟨by decide, 1, rfl, ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩, by decide⟩
  exact (IsGenCohnMatrix.mul_E_mul hM).2

end MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessMulEMul
