/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadData

/-! Original preferred source syndrome and coefficient in actual physical coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual source syndrome read directly from its two physical coordinates. -/
def generatedSixthMiddleOctadSyndrome (k : Fin 273) : SpinIndex := fun j =>
  (golayGeneratorBit j (generatedSixthMiddleOctadSourceCoordinates k).2.1 : ZMod 2) +
    (golayGeneratorBit j (generatedSixthMiddleOctadSourceCoordinates k).2.2 : ZMod 2)

/-- The physical formula agrees with the genuine preferred pair's syndrome. -/
theorem generatedSixth_middle_octad_input_syndrome (k : Fin 273) :
    griessPairSyndrome (generatedSixthMiddleOctadInput k).2 =
      generatedSixthMiddleOctadSyndrome k := by
  funext j
  change (golayGeneratorBit j (griessCoordinatePair
    (griessPairIndex (generatedSixthMiddleOctadSourceCoordinates k).2.1
      (generatedSixthMiddleOctadSourceCoordinates k).2.2
      (ne_of_lt (generatedSixth_middle_octad_source_lt k)))).1 : ZMod 2) +
    (golayGeneratorBit j (griessCoordinatePair
      (griessPairIndex (generatedSixthMiddleOctadSourceCoordinates k).2.1
        (generatedSixthMiddleOctadSourceCoordinates k).2.2
      (ne_of_lt (generatedSixth_middle_octad_source_lt k)))).2 : ZMod 2) = _
  rw [griessPairIndex_coordinates, ite_eq_left (generatedSixth_middle_octad_source_lt k)]
  rfl

/-- The exact original signed pair coefficient numerator in physical coordinates. -/
def generatedSixthMiddleOctadSourceWeight (k : Fin 273) : ℤ :=
  (if (generatedSixthMiddleOctadSourceCoordinates k).1 = 0 then 1 else -1) *
    griessShortIntegral (Sum.inr (Sum.inr (0,0)))
      (generatedSixthMiddleOctadSourceCoordinates k).2.1 *
    griessShortIntegral (Sum.inr (Sum.inr (0,0)))
      (generatedSixthMiddleOctadSourceCoordinates k).2.2

/-- The physical numerator equals the original genuine pair-address coefficient. -/
theorem generatedSixth_middle_octad_input_weight (k : Fin 273) :
    generatedSixthSourceShortWeight (generatedSixthMiddleOctadInput k) =
      generatedSixthMiddleOctadSourceWeight k := by
  unfold generatedSixthSourceShortWeight generatedSixthMiddleOctadInput
  rw [griessPairIndex_coordinates, ite_eq_left (generatedSixth_middle_octad_source_lt k)]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
