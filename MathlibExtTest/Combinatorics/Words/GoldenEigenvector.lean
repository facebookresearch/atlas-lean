/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.GoldenEigenvector

/-! # Tests for integer matrices with the golden eigenvector -/

namespace MetaMathlibExt.golden_eigenvector_iff

-- Negative off-diagonal entries are allowed.
example : ∃ c : ℝ, ((!![0, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.cast : ℤ → ℝ)).mulVec ![Real.goldenRatio, 1] = c • ![Real.goldenRatio, 1] :=
  (golden_eigenvector_iff _).1.2 ⟨-1, 1, by norm_num⟩

-- The two off-diagonal entries must agree.
example : ¬ ∃ c : ℝ, ((!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.cast : ℤ → ℝ)).mulVec ![Real.goldenRatio, 1] = c • ![Real.goldenRatio, 1] := by
  rw [(golden_eigenvector_iff _).1]
  rintro ⟨m, n, h⟩
  have h01 : (1 : ℤ) = m := congrFun (congrFun h 0) 1
  have h10 : (0 : ℤ) = m := congrFun (congrFun h 1) 0
  omega

-- When the off-diagonal entries vanish, both roots coincide.
open Polynomial in
example (n : ℤ) : ((!![n, 0; 0, n] : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.cast : ℤ → ℝ)).charpoly = (X - C (n : ℝ)) ^ 2 := by
  simpa [sq] using (golden_eigenvector_iff !![n, 0; 0, n]).2 0 n (by simp)

end MetaMathlibExt.golden_eigenvector_iff
