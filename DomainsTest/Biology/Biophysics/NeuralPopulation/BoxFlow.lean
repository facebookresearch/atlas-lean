/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.Biophysics.NeuralPopulation.BoxFlow

/-! Tests: box projection onto `[0, 2]^2`. -/

namespace MathlibExtTest.Biology.Biophysics.NeuralPopulation.BoxFlow

open MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-- The first projected coordinate at `5` is the upper endpoint `2`. -/
example : (((boxProj 2 zero_le_two (fun _ => (5:ℝ)) : Set.Icc (0 : Fin 2 → ℝ) (fun _ => 2)) : Fin 2 → ℝ) 0) = 2 := by
  rw [boxProj_apply]
  have h : min (2:ℝ) 5 = 2 := min_eq_left (show (2:ℝ) ≤ 5 by exact_mod_cast (by decide : (2:ℕ) ≤ 5))
  rw [h]
  exact max_eq_right (show (0:ℝ) ≤ 2 by exact_mod_cast (by decide : (0:ℕ) ≤ 2))

/-- An interior state projects to itself. -/
example : ((boxProj 2 zero_le_two (fun _ => (1:ℝ)) : Set.Icc (0 : Fin 2 → ℝ) (fun _ => 2)) : Fin 2 → ℝ) =
    (fun _ => (1:ℝ)) :=
  boxProj_of_mem 2 zero_le_two (Set.mem_Icc.mpr ⟨fun _ => zero_le_one, fun _ => one_le_two⟩)

end MathlibExtTest.Biology.Biophysics.NeuralPopulation.BoxFlow
