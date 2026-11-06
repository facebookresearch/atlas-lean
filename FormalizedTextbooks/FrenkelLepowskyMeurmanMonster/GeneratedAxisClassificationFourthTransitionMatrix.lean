/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddLocalLift

/-! Exact original matrix coordinates for the next triality transition.
These identities expose the finite short-coordinate obligations for a new
actual representative, without assigning it a source conjugacy-class label. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original triality fixes every diagonal matrix coordinate. -/
theorem generatedFourth_triality_matrix_diagonal (x : GriessSpace) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).1 i i = (griessConwayEncode x).1 i i := by
  simp [griessConwayEncode, sExtra, griessTriality, trialityBlockAction]

/-- Original triality obtains each off-diagonal matrix coordinate from the
sum of its two actual preferred pair-short coordinates. -/
theorem generatedFourth_triality_matrix_off_diagonal (x : GriessSpace)
    (i j : Fin 24) (hij : i ≠ j) :
    (griessConwayEncode (sExtra x)).1 i j =
      ((griessConwayEncode x).2.1 (Sum.inl (0, griessPairIndex i j hij)) +
        (griessConwayEncode x).2.1 (Sum.inl (1, griessPairIndex i j hij))) / 2 := by
  have hc : trialityCycle.symm 0 = 2 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, trialityBlockAction,
    trialityCycleAction, hc, hij]
  ring

/-- The whole actual triality matrix is determined by the original diagonal
and the 552 genuine preferred pair-short coefficients. -/
theorem generatedFourth_triality_matrix (x : GriessSpace) :
    (griessConwayEncode (sExtra x)).1 = fun i j =>
      if h : i = j then (griessConwayEncode x).1 i i else
        ((griessConwayEncode x).2.1 (Sum.inl (0, griessPairIndex i j h)) +
          (griessConwayEncode x).2.1 (Sum.inl (1, griessPairIndex i j h))) / 2 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [dite_true]
    exact generatedFourth_triality_matrix_diagonal x i
  · simp only [dite_eq_right h]
    exact generatedFourth_triality_matrix_off_diagonal x i j h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
