/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.UnitStepWalkThreeTermProgressionErdosProblem192

open MathlibExt.Combinatorics.UnitStepWalkThreeTermProgressionErdosProblem192Wanted

-- Dimension zero is included, but cannot supply even the first step.
example (a : ℕ → Fin 0 → ℝ) : ¬ IsUnitStepWalk 0 a := by
  intro ha
  obtain ⟨j, _⟩ := ha 0
  exact Fin.elim0 j

-- The largest forced dimension and the first dimension admitting a counterexample.
example (a : ℕ → Fin 3 → ℝ) (ha : IsUnitStepWalk 3 a) : HasThreeAP a :=
  (unitStepWalkThreeAPIff_holds 3).mpr le_rfl a ha

example : ∃ a : ℕ → Fin 4 → ℝ, IsUnitStepWalk 4 a ∧ ¬ HasThreeAP a := by
  by_contra h
  apply (by decide : ¬ (4 : ℕ) ≤ 3)
  apply (unitStepWalkThreeAPIff_holds 4).mp
  intro a ha
  by_contra hno
  exact h ⟨a, ha, hno⟩

-- The arithmetic equation by itself does not make a constant sequence a progression.
example : ¬ HasThreeAP (d := 1) (fun _ _ ↦ 0) := by
  rintro ⟨_, _, _, hne, _⟩
  exact hne rfl

-- The public predicate does not require the indices to be listed in chronological order.
example : HasThreeAP (d := 1) (fun n _ ↦ (n : ℝ)) := by
  refine ⟨2, 1, 0, ?_, ?_⟩
  · intro h
    have he : ((2 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) := congrFun h (0 : Fin 1)
    exact (by decide : (2 : ℕ) ≠ 1) (by exact_mod_cast he)
  · rw [two_nsmul]
    funext c
    simpa using (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
