/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortActualCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMiddleShortSupport

/-! The genuine local word transports the complete counted support bijectively. Its original
scalar signs are nonzero, so the middle axis also has exactly3856 nonzero short coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual nonzero preferred short coordinates after the original local word. -/
abbrev generatedNinthMiddleActualShortSupport :=
  {r : GriessShortIndex // (griessConwayEncode
    (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis)).2.1 r ≠ 0}

private theorem ninthActualShortPhase_ne_zero (c : ZMod 2) : qSign c ≠ 0 := by
  intro h
  have hs := qSign_sq c
  rw [h, zero_mul] at hs
  norm_num at hs

/-- Include every counted nonzero source at its actual transported coordinate. -/
def generatedNinthMiddleShortSupportMap :
    generatedNinthOriginalShortSupport → generatedNinthMiddleActualShortSupport := fun a =>
  ⟨generatedNinthMiddleShortSourceIndex a.val, by
    rw [generatedNinth_middle_short_source_coefficient]
    exact mul_ne_zero (ninthActualShortPhase_ne_zero _)
      (div_ne_zero (by exact_mod_cast a.property) (by norm_num))⟩

/-- The actual preferred-short permutation preserves distinct source indices. -/
theorem generatedNinth_middle_short_support_map_injective :
    Function.Injective generatedNinthMiddleShortSupportMap := by
  intro a b h
  apply Subtype.ext
  apply generatedNinth_original_short_index_injective
  apply (griessShortPermutation generatedNinthLocalFiber.val.2).injective
  exact congrArg Subtype.val h

/-- The full source-coverage theorem covers every nonzero actual transported coordinate. -/
theorem generatedNinth_middle_short_support_map_surjective :
    Function.Surjective generatedNinthMiddleShortSupportMap := by
  intro r
  obtain ⟨a, ha, hn⟩ := generatedNinth_middle_short_nonzero_covered r.val r.property
  exact ⟨⟨a, hn⟩, Subtype.ext ha⟩

/-- The original source support equals the full nonzero support after the actual local word. -/
def generatedNinthMiddleActualShortSupportEquiv :
    generatedNinthOriginalShortSupport ≃ generatedNinthMiddleActualShortSupport :=
  Equiv.ofBijective generatedNinthMiddleShortSupportMap
    ⟨generatedNinth_middle_short_support_map_injective,
      generatedNinth_middle_short_support_map_surjective⟩

/-- The original local word has exactly3856 genuine nonzero middle short coordinates. -/
theorem generatedNinth_middle_actual_short_support_card :
    Fintype.card generatedNinthMiddleActualShortSupport = 3856 := by
  rw [← Fintype.card_congr generatedNinthMiddleActualShortSupportEquiv,
    generatedNinth_original_short_support_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
