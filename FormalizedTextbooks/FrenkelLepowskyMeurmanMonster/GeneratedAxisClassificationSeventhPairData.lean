/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts

/-! Three preferred pair addresses and their genuine Golay syndromes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Physical source coordinate pairs for the three selected rows. -/
def generatedSeventhSourceCoordinates : Fin 3 → Fin 24 × Fin 24 :=
  ![(12, 14), (12, 15), (14, 15)]

/-- Physical target coordinate pairs for the three selected rows. -/
def generatedSeventhTargetCoordinates : Fin 3 → Fin 24 × Fin 24 :=
  ![(16, 17), (16, 19), (17, 19)]

/-- The selected source coordinates are in increasing order. -/
theorem generatedSeventh_source_coordinates_lt (j : Fin 3) :
    (generatedSeventhSourceCoordinates j).1 < (generatedSeventhSourceCoordinates j).2 := by
  fin_cases j <;> decide

/-- The selected target coordinates are in increasing order. -/
theorem generatedSeventh_target_coordinates_lt (j : Fin 3) :
    (generatedSeventhTargetCoordinates j).1 < (generatedSeventhTargetCoordinates j).2 := by
  fin_cases j <;> decide

/-- The three genuine source pair indices in the original short catalogue. -/
def generatedSeventhSourcePair (j : Fin 3) : Fin 276 :=
  griessPairIndex (generatedSeventhSourceCoordinates j).1 (generatedSeventhSourceCoordinates j).2
    (ne_of_lt (generatedSeventh_source_coordinates_lt j))

/-- Their three genuine target pair indices in the original short catalogue. -/
def generatedSeventhTargetPair (j : Fin 3) : Fin 276 :=
  griessPairIndex (generatedSeventhTargetCoordinates j).1 (generatedSeventhTargetCoordinates j).2
    (ne_of_lt (generatedSeventh_target_coordinates_lt j))

/-- Source modulation masks for the three preferred lifts. -/
def generatedSeventhSourceModulation : Fin 3 → Fin 4096 := ![1360, 2032, 672]

/-- Target modulation masks for the three preferred lifts. -/
def generatedSeventhTargetModulation : Fin 3 → Fin 4096 := ![1504, 1648, 912]

/-- Both pair-index arrays refer to their stated actual physical coordinate pairs. -/
theorem generatedSeventh_pair_coordinate_certificate : ∀ j : Fin 3,
    griessCoordinatePair (generatedSeventhSourcePair j) = ![(12, 14), (12, 15), (14, 15)] j ∧
      griessCoordinatePair (generatedSeventhTargetPair j) = ![(16, 17), (16, 19), (17, 19)] j := by
  intro j
  simp only [generatedSeventhSourcePair, generatedSeventhTargetPair, griessPairIndex_coordinates,
    generatedSeventh_source_coordinates_lt, generatedSeventh_target_coordinates_lt, ite_true]
  exact ⟨rfl, rfl⟩

/-- The masks are the genuine preferred-pair syndromes, with no change of source convention. -/
theorem generatedSeventh_pair_syndrome_certificate : ∀ j : Fin 3,
    griessPairSyndrome (generatedSeventhSourcePair j) =
      golayLabelCoefficients (generatedSeventhSourceModulation j) ∧
    griessPairSyndrome (generatedSeventhTargetPair j) =
      golayLabelCoefficients (generatedSeventhTargetModulation j) := by
  intro j
  constructor
  · ext k
    change (golayGeneratorBit k (griessCoordinatePair (generatedSeventhSourcePair j)).1 : ZMod 2) +
      (golayGeneratorBit k (griessCoordinatePair (generatedSeventhSourcePair j)).2 : ZMod 2) = _
    rw [(generatedSeventh_pair_coordinate_certificate j).1]
    fin_cases j <;> fin_cases k <;> decide +kernel
  · ext k
    change (golayGeneratorBit k (griessCoordinatePair (generatedSeventhTargetPair j)).1 : ZMod 2) +
      (golayGeneratorBit k (griessCoordinatePair (generatedSeventhTargetPair j)).2 : ZMod 2) = _
    rw [(generatedSeventh_pair_coordinate_certificate j).2]
    fin_cases j <;> fin_cases k <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
