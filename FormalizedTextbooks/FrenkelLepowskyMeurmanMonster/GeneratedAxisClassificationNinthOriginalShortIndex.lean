/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortQCoordinates

/-! The complete original source catalogue has no repeated actual preferred short index. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 4000000 in
-- Check only the56 original code labels, without computing their sorted catalogue inverses.
/-- The supported original octad code labels are distinct. -/
theorem generatedNinth_original_octad_code_injective :
    Function.Injective generatedFifthEvenRootCode := by
  intro a b h
  have hc : ∀ a b : Fin 56, generatedFifthEvenRootCode a = generatedFifthEvenRootCode b →
      a = b := by decide +kernel
  exact hc a b h

/-- Distinct original source octads have distinct genuine preferred catalogue indices. -/
theorem generatedNinth_original_octad_index_injective :
    Function.Injective generatedFifthEvenRootOctad := by
  intro a b h
  apply generatedNinth_original_octad_code_injective
  simpa only [generatedFifthEvenRootOctad_label] using congrArg golayOctadLabel h

/-- The complete original source catalogue embeds in the actual short-coordinate dictionary. -/
theorem generatedNinth_original_short_index_injective :
    Function.Injective generatedNinthOriginalShortIndex := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b =>
      have hp := Sum.inl.inj (Sum.inr.inj h)
      have hj := generatedNinth_original_octad_index_injective (congrArg Prod.fst hp)
      have he := congrArg Prod.snd hp
      exact congrArg Sum.inr (Prod.ext hj he)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
