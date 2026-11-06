/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadCoordinates
public import Mathlib.Order.Fin.Basic

/-! The displayed actual octad images are distinct genuine source and target addresses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Lexicographic physical pair order, with the preferred sign as the final binary digit. -/
def generatedSixthMiddleOctadSourceOrder (k : Fin 273) : ℕ :=
  2 * (24 * (generatedSixthMiddleOctadSourceCoordinates k).2.1.val +
    (generatedSixthMiddleOctadSourceCoordinates k).2.2.val) +
      (generatedSixthMiddleOctadSourceCoordinates k).1.val

/-- The actual source list is strictly ordered without assigning numeric pair catalogue labels. -/
theorem generatedSixthMiddleOctadSourceOrder_strictMono :
    StrictMono generatedSixthMiddleOctadSourceOrder := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

/-- Distinct displayed entries are distinct genuine physical source-pair addresses. -/
theorem generatedSixthMiddleOctadInput_injective :
    Function.Injective generatedSixthMiddleOctadInput := by
  intro k l h
  apply generatedSixthMiddleOctadSourceOrder_strictMono.injective
  have he := congrArg (fun p : GeneratedSixthSourcePair =>
    2 * (24 * (griessCoordinatePair p.2).1.val + (griessCoordinatePair p.2).2.val) + p.1.val) h
  simpa only [generatedSixthMiddleOctadInput, generatedSixthMiddleOctadSourceOrder,
    griessPairIndex_coordinates, generatedSixth_middle_octad_source_lt, ite_true] using he

/-- All 273 displayed outputs are distinct labels in the genuine preferred short catalogue. -/
theorem generatedSixthMiddleOctadOutput_injective :
    Function.Injective generatedSixthMiddleOctadOutput := by
  intro k l h
  apply generatedSixthMiddleOctadInput_injective
  apply generatedSixth_middle_short_label_injective
  rw [generatedSixth_middle_octad_permutation, generatedSixth_middle_octad_permutation]
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
