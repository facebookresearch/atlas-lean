/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts

/-! Eight full preferred-Q transports, using genuine pair-coordinate addresses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original signed pair coordinates in the bounded packet. -/
def generatedSixthMiddleShortPacket00Coordinates : Fin 8 → Fin 2 × Fin 24 × Fin 24 :=
  ![(0, 0, 1),
    (1, 0, 1),
    (0, 0, 2),
    (1, 0, 2),
    (0, 0, 3),
    (1, 0, 3),
    (0, 0, 4),
    (1, 0, 4)]

/-- The genuine source coordinates are distinct and increasing. -/
theorem generatedSixth_middle_short_packet00_coordinate_lt (j : Fin 8) :
    (generatedSixthMiddleShortPacket00Coordinates j).2.1 <
      (generatedSixthMiddleShortPacket00Coordinates j).2.2 := by
  fin_cases j <;> decide

/-- Original preferred pair addresses, constructed from their actual coordinates. -/
def generatedSixthMiddleShortPacket00Input (j : Fin 8) : GeneratedSixthSourcePair :=
  ((generatedSixthMiddleShortPacket00Coordinates j).1,
    griessPairIndex (generatedSixthMiddleShortPacket00Coordinates j).2.1
      (generatedSixthMiddleShortPacket00Coordinates j).2.2
      (ne_of_lt (generatedSixth_middle_short_packet00_coordinate_lt j)))

/-- Original finite translation and modulation masks before the local word. -/
def generatedSixthMiddleShortPacket00InitialData : Fin 8 → Fin 4096 × Fin 4096 :=
  ![(0, 1536),
    (2048, 1536),
    (0, 1280),
    (2048, 1280),
    (0, 1792),
    (2048, 1792),
    (0, 1039),
    (2048, 1039)]

/-- The genuine original pair lifts, in literal translation and modulation coordinates. -/
def generatedSixthMiddleShortPacket00InitialQ (j : Fin 8) : Q :=
  generatedAxisFourthQFromSpin
    (golayLabelCoefficients (generatedSixthMiddleShortPacket00InitialData j).1)
    (golayLabelCoefficients (generatedSixthMiddleShortPacket00InitialData j).2) 0

/-- Every original full target coordinate, including its preferred central phase. -/
def generatedSixthMiddleShortPacket00FinalQ : Fin 8 → Q :=
  ![generatedAxisFourthQFromSpin (golayLabelCoefficients 3065)
      (golayLabelCoefficients 2494) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 11)
      (golayLabelCoefficients 292) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1972)
      (golayLabelCoefficients 2015) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3142)
      (golayLabelCoefficients 3909) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 2004)
      (golayLabelCoefficients 1070) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3110)
      (golayLabelCoefficients 3252) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1473)
      (golayLabelCoefficients 3682) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3635)
      (golayLabelCoefficients 1784) 0]

/-- The modulation masks are the genuine Golay pair syndromes. -/
theorem generatedSixth_middle_short_packet00_syndrome (j : Fin 8) :
    griessPairSyndrome (generatedSixthMiddleShortPacket00Input j).2 =
      golayLabelCoefficients (generatedSixthMiddleShortPacket00InitialData j).2 := by
  unfold griessPairSyndrome generatedSixthMiddleShortPacket00Input
  rw [griessPairIndex_coordinates,
    ite_eq_left (generatedSixth_middle_short_packet00_coordinate_lt j)]
  fin_cases j <;> decide +kernel

/-- The literal source Q data equal the genuine preferred pair lifts. -/
theorem generatedSixth_middle_short_packet00_initial (j : Fin 8) :
    generatedSixthMiddleShortPacket00InitialQ j =
      griessShortQ (Sum.inl (generatedSixthMiddleShortPacket00Input j)) := by
  unfold generatedSixthMiddleShortPacket00InitialQ
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation, griessPairQ_translation]
    fin_cases j <;> decide +kernel
  · rw [generatedAxisFourthQFromSpin_modulation,
      griessPairQ_modulation, generatedSixth_middle_short_packet00_syndrome]
  · rw [generatedAxisFourthQFromSpin_coeff, griessShortQ_coeff]

set_option maxHeartbeats 4000000 in
-- Evaluate eight original full Q images against literal source and target coordinates.
/-- Every full Q image retains its actual target and preferred central sign. -/
theorem generatedSixth_middle_short_packet00_Q_certificate (j : Fin 8) :
    generatedSixthQImage (generatedSixthMiddleShortPacket00InitialQ j) =
      generatedSixthMiddleShortPacket00FinalQ j := by
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

/-- The original spin normalizer realizes these exact preferred source Q transports. -/
theorem generatedSixth_middle_short_packet00_Q_image (j : Fin 8) :
    spinConjugation generatedSixthLocalFiber.val.1
      (griessShortQ (Sum.inl (generatedSixthMiddleShortPacket00Input j))) =
        generatedSixthMiddleShortPacket00FinalQ j := by
  rw [← generatedSixth_middle_short_packet00_initial, generatedSixth_spin_conjugation,
    generatedSixth_middle_short_packet00_Q_certificate]

/-- The packet signs are the central phases of the genuine local short action. -/
theorem generatedSixth_middle_short_packet00_phase (j : Fin 8) :
    generatedSixthMiddleShortPhase (generatedSixthMiddleShortPacket00Input j) =
      Multiplicative.toAdd (generatedSixthMiddleShortPacket00FinalQ j).coeff := by
  unfold generatedSixthMiddleShortPhase localShortPhase
  rw [generatedSixth_middle_short_packet00_Q_image]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
