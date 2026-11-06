/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthRepresentative

/-! Bind the integer input certificates to the genuine preferred-short catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine preferred input for each of the 64 listed odd output roots. -/
noncomputable def generatedFifthOddRootInputLabel (j : Fin 64) : GriessShortIndex :=
  match h : generatedFifthOddRootInputData j with
  | Sum.inl (s, a, b) => Sum.inl (s, griessPairIndex a b (by
      have hl := generatedFifthOddRootInputData_lt j
      rw [h] at hl
      exact ne_of_lt hl))
  | Sum.inr e => Sum.inr (Sum.inl (generatedFourthOctad, e))

/-- The computational physical input is exactly the genuine preferred vector. -/
theorem generatedFifthOddRootInputLabel_integral (j : Fin 64) :
    griessShortIntegral (generatedFifthOddRootInputLabel j) =
      generatedFifthOddRootInputIntegral j := by
  have hl := generatedFifthOddRootInputData_lt j
  unfold generatedFifthOddRootInputLabel
  split <;> simp_all [griessShortIntegral, generatedFifthOddRootInputIntegral,
    griessPairIndex_coordinates, generatedFourthOctad_mask, generatedFourth_root_sign_mask]

/-- Every checked physical overall sign is exactly plus or minus one. -/
theorem generatedFifthOddRootPhysicalSign_unit : ∀ j : Fin 64,
    generatedFifthOddRootPhysicalSign j = 1 ∨ generatedFifthOddRootPhysicalSign j = -1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
