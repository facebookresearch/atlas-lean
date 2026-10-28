/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord

/-! Bind the integer input certificates to the genuine preferred-short catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine preferred input for each of the 56 listed odd output roots. -/
noncomputable def generatedFourthOddRootInputLabel (j : Fin 56) : GriessShortIndex :=
  match h : generatedFourthOddRootInputData j with
  | Sum.inl (s, a, b) => Sum.inl (s, griessPairIndex a b (by
      have hl := generatedFourthOddRootInputData_lt j
      rw [h] at hl
      exact ne_of_lt hl))
  | Sum.inr e => Sum.inr (Sum.inl (generatedFourthOctad, e))

/-- The computational physical input is exactly the genuine preferred vector. -/
theorem generatedFourthOddRootInputLabel_integral (j : Fin 56) :
    griessShortIntegral (generatedFourthOddRootInputLabel j) =
      generatedFourthOddRootInputIntegral j := by
  have hl := generatedFourthOddRootInputData_lt j
  unfold generatedFourthOddRootInputLabel
  split <;> simp_all [griessShortIntegral, generatedFourthOddRootInputIntegral,
    griessPairIndex_coordinates, generatedFourthOctad_mask, generatedFourth_root_sign_mask]

/-- Every checked physical overall sign is exactly plus or minus one. -/
theorem generatedFourthOddRootPhysicalSign_unit : ∀ j : Fin 56,
    generatedFourthOddRootPhysicalSign j = 1 ∨ generatedFourthOddRootPhysicalSign j = -1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
