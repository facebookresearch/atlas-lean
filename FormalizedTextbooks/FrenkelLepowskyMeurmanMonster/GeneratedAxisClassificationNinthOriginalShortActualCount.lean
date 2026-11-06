/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortIndex

/-! The finite source count counts genuine nonzero short coordinates, not repeated labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual nonzero preferred short coordinates of the original generated fifth axis. -/
abbrev generatedNinthOriginalActualShortSupport :=
  {r : GriessShortIndex // (griessConwayEncode generatedFifthAxis).2.1 r ≠ 0}

/-- Include each counted nonzero source row into the actual coordinate support. -/
def generatedNinthOriginalShortSupportMap :
    generatedNinthOriginalShortSupport → generatedNinthOriginalActualShortSupport := fun a =>
  ⟨generatedNinthOriginalShortIndex a.val, by
    rw [generatedNinth_original_short_numerator_actual]
    exact div_ne_zero (by exact_mod_cast a.property) (by norm_num)⟩

/-- No two counted nonzero source rows describe the same genuine coordinate. -/
theorem generatedNinth_original_short_support_map_injective :
    Function.Injective generatedNinthOriginalShortSupportMap := by
  intro a b h
  apply Subtype.ext
  exact generatedNinth_original_short_index_injective (congrArg Subtype.val h)

/-- Every actual nonzero preferred short coordinate is represented by a counted source row. -/
theorem generatedNinth_original_short_support_map_surjective :
    Function.Surjective generatedNinthOriginalShortSupportMap := by
  intro r
  obtain ⟨a, ha⟩ := generatedNinth_original_short_nonzero_covered r.val r.property
  have hn : generatedNinthOriginalShortNumerator a ≠ 0 :=
    generatedNinth_original_short_numerator_ne_zero a (ha.symm ▸ r.property)
  exact ⟨⟨a, hn⟩, Subtype.ext ha⟩

/-- The source support is equivalent to the complete actual nonzero coordinate support. -/
def generatedNinthOriginalActualShortSupportEquiv :
    generatedNinthOriginalShortSupport ≃ generatedNinthOriginalActualShortSupport :=
  Equiv.ofBijective generatedNinthOriginalShortSupportMap
    ⟨generatedNinth_original_short_support_map_injective,
      generatedNinth_original_short_support_map_surjective⟩

/-- Exactly3856 genuine preferred short coordinates of the original axis are nonzero. -/
theorem generatedNinth_original_actual_short_support_card :
    Fintype.card generatedNinthOriginalActualShortSupport = 3856 := by
  rw [← Fintype.card_congr generatedNinthOriginalActualShortSupportEquiv,
    generatedNinth_original_short_support_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
