/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LeftoverHash
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open InformationTheory

/-- The uniform distribution on two points has collision probability at most `1/2`. -/
example : ∑ _x : Fin 2, ((1 / 2 : ℝ)) ^ 2 ≤ 1 / 2 :=
  collision_le_of_le (fun _ => 1 / 2) (fun _ => by norm_num)
    (by simp) _ (fun _ => le_refl _)

/-- The masses `1/4` and `3/4` have collision probability `5/8`. -/
example : ∑ x : Fin 2, (![1 / 4, 3 / 4] x : ℝ) ^ 2 = 5 / 8 := by
  simp [Fin.sum_univ_two]
  norm_num

/-- The bound by the largest mass `3/4` for the masses `1/4` and `3/4`. -/
example : ∑ x : Fin 2, (![1 / 4, 3 / 4] x : ℝ) ^ 2 ≤ 3 / 4 :=
  collision_le_of_le _ (fun x => by fin_cases x <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) _ (fun x => by fin_cases x <;> norm_num)

/-- `collision_le_max'` with the nonemptiness point `0`, which has the smaller mass `1/4`. -/
example : ∑ x : Fin 2, (![1 / 4, 3 / 4] x : ℝ) ^ 2 ≤
    (Finset.univ.image (![1 / 4, 3 / 4] : Fin 2 → ℝ)).max'
      ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩ :=
  collision_le_max' _ (fun x => by fin_cases x <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) 0

end
