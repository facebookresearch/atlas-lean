/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts

/-! Three preferred pair addresses and their genuine Golay syndromes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Physical source coordinate pairs for the three selected rows. -/
def generatedSixthSourceCoordinates : Fin 3 → Fin 24 × Fin 24 :=
  ![(12, 16), (0, 12), (0, 16)]

/-- Physical target coordinate pairs for the three selected rows. -/
def generatedSixthTargetCoordinates : Fin 3 → Fin 24 × Fin 24 :=
  ![(16, 17), (16, 19), (17, 19)]

/-- The selected source coordinates are in increasing order. -/
theorem generatedSixth_source_coordinates_lt (j : Fin 3) :
    (generatedSixthSourceCoordinates j).1 < (generatedSixthSourceCoordinates j).2 := by
  fin_cases j <;> decide

/-- The selected target coordinates are in increasing order. -/
theorem generatedSixth_target_coordinates_lt (j : Fin 3) :
    (generatedSixthTargetCoordinates j).1 < (generatedSixthTargetCoordinates j).2 := by
  fin_cases j <;> decide

/-- The three genuine source pair indices in the original short catalogue. -/
def generatedSixthSourcePair (j : Fin 3) : Fin 276 :=
  griessPairIndex (generatedSixthSourceCoordinates j).1 (generatedSixthSourceCoordinates j).2
    (ne_of_lt (generatedSixth_source_coordinates_lt j))

/-- Their three genuine target pair indices in the original short catalogue. -/
def generatedSixthTargetPair (j : Fin 3) : Fin 276 :=
  griessPairIndex (generatedSixthTargetCoordinates j).1 (generatedSixthTargetCoordinates j).2
    (ne_of_lt (generatedSixth_target_coordinates_lt j))

/-- Source modulation masks for the three preferred lifts. -/
def generatedSixthSourceModulation : Fin 3 → Fin 4096 := ![6, 1037, 1035]

/-- Target modulation masks for the three preferred lifts. -/
def generatedSixthTargetModulation : Fin 3 → Fin 4096 := ![1504, 1648, 912]

/-- Both pair-index arrays refer to their stated actual physical coordinate pairs. -/
theorem generatedSixth_pair_coordinate_certificate : ∀ j : Fin 3,
    griessCoordinatePair (generatedSixthSourcePair j) = ![(12, 16), (0, 12), (0, 16)] j ∧
      griessCoordinatePair (generatedSixthTargetPair j) = ![(16, 17), (16, 19), (17, 19)] j := by
  intro j
  simp only [generatedSixthSourcePair, generatedSixthTargetPair, griessPairIndex_coordinates,
    generatedSixth_source_coordinates_lt, generatedSixth_target_coordinates_lt, ite_true]
  exact ⟨rfl, rfl⟩

/-- The masks are the genuine preferred-pair syndromes, with no change of source convention. -/
theorem generatedSixth_pair_syndrome_certificate : ∀ j : Fin 3,
    griessPairSyndrome (generatedSixthSourcePair j) =
      golayLabelCoefficients (generatedSixthSourceModulation j) ∧
    griessPairSyndrome (generatedSixthTargetPair j) =
      golayLabelCoefficients (generatedSixthTargetModulation j) := by
  intro j
  constructor
  · ext k
    change (golayGeneratorBit k (griessCoordinatePair (generatedSixthSourcePair j)).1 : ZMod 2) +
      (golayGeneratorBit k (griessCoordinatePair (generatedSixthSourcePair j)).2 : ZMod 2) = _
    rw [(generatedSixth_pair_coordinate_certificate j).1]
    fin_cases j <;> fin_cases k <;> decide +kernel
  · ext k
    change (golayGeneratorBit k (griessCoordinatePair (generatedSixthTargetPair j)).1 : ZMod 2) +
      (golayGeneratorBit k (griessCoordinatePair (generatedSixthTargetPair j)).2 : ZMod 2) = _
    rw [(generatedSixth_pair_coordinate_certificate j).2]
    fin_cases j <;> fin_cases k <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
