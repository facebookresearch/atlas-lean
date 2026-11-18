/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-! Tests: box projection onto `[0, 2]`. -/

namespace MathlibExtTest.Biology.Biophysics.NeuralPopulation.BoxFlow

open MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-- A value inside the box projects to itself. -/
example : boxProj 2 zero_le_two (1:ℝ) =
    ⟨1, ⟨by exact_mod_cast (by decide : (0:ℕ) ≤ 1),
      by exact_mod_cast (by decide : (1:ℕ) ≤ 2)⟩⟩ :=
  boxProj_of_mem 2 zero_le_two
    ⟨by exact_mod_cast (by decide : (0:ℕ) ≤ 1),
      by exact_mod_cast (by decide : (1:ℕ) ≤ 2)⟩

/-- The projected value at `5` is the upper endpoint `2`. -/
example : ((boxProj 2 zero_le_two (5:ℝ) : Set.Icc (0:ℝ) 2) : ℝ) = 2 := by
  rw [boxProj_coe]
  have h : min (2:ℝ) 5 = 2 := min_eq_left (show (2:ℝ) ≤ 5 by exact_mod_cast (by decide : (2:ℕ) ≤ 5))
  rw [h]
  exact max_eq_right (show (0:ℝ) ≤ 2 by exact_mod_cast (by decide : (0:ℕ) ≤ 2))

end MathlibExtTest.Biology.Biophysics.NeuralPopulation.BoxFlow
