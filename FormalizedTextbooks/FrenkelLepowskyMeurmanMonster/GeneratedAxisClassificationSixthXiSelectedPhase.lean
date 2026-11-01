/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiQCoordinateEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQSelectedPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhase

/-! Checked scalar pairings evaluate the complete original Xi phase without Q products. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Packed scalar pairings of all genuine corrected-Xi coordinate images. -/
def generatedSixthXiCoordinatePairMasks : Fin 24 → ℕ :=
  ![9679428, 8398740, 16580963, 1283712, 9049922, 9507460,
    6418965, 8959274, 8959638, 1680763, 1000346, 0,
    504, 961, 8389700, 961, 8390269, 8389689,
    8389700, 8390420, 813, 580, 8389700, 5196215]

/-- Every displayed pairing bit retains the original cocycle orientation. -/
def generatedSixthXiCoordinatePairPhase (i j : Fin 24) : ZMod 2 :=
  if (generatedSixthXiCoordinatePairMasks i).testBit j.val then 1 else 0

set_option maxHeartbeats 16000000 in
-- Check all 576 actual image pairings against their displayed scalar bits.
/-- All 576 pairings equal the genuine cocycle pairings of the checked full images. -/
theorem generatedSixth_xi_coordinate_pair_phase_actual (i j : Fin 24) :
    qBeta (toAdd (generatedSixthXiCoordinateImage i).base)
      (toAdd (generatedSixthXiCoordinateImage j).base) =
        generatedSixthXiCoordinatePairPhase i j := by
  revert i j
  decide +kernel

/-- Exact scalar Xi phase, including the input normal-form and image central corrections. -/
def generatedSixthXiSelectedPhase (q : Q) : ZMod 2 :=
  toAdd q.coeff + generatedSixthQSelectedPhase (fun _ => 0)
    monsterNortonCoordinatePairPhase (toAdd q.base) (List.finRange 24) +
    generatedSixthQSelectedPhase
      (fun i => (generatedSixthXiCoordinateImageLabels i).2.2)
      generatedSixthXiCoordinatePairPhase (toAdd q.base) (List.finRange 24)

/-- The scalar formula is the genuine corrected original spin-conjugation central coefficient. -/
theorem generatedSixth_xi_selected_phase (q : Q) :
    toAdd (spinConjugation (generatedSixthCorrectedGenerator 4).val.1 q).coeff =
      generatedSixthXiSelectedPhase q := by
  rw [generatedSixth_xi_QImage, generatedSixth_xi_QCoordinateEvaluation_eq]
  rw [generatedSixthXiQCoordinateEvaluation, monsterNortonCoordinateEvaluation_finite_phase,
    List.ofFn_eq_map, List.ofFn_eq_map]
  rw [generatedSixth_Q_selected_phase_actual _ _ _ (fun _ => rfl)
    monsterNortonCoordinatePairPhase_actual]
  rw [generatedSixth_Q_selected_phase_actual _ _ _ (fun _ => rfl)
    generatedSixth_xi_coordinate_pair_phase_actual]
  rfl

/-- The complete original short-coordinate phase depends on its genuine preferred source lift. -/
theorem generatedSixth_xi_short_selected_phase (r : GriessShortIndex) :
    localShortPhase (generatedSixthCorrectedGenerator 4) r =
      generatedSixthXiSelectedPhase (griessShortQ r) :=
  generatedSixth_xi_selected_phase (griessShortQ r)

/-- Actual output-label recognition gives the complete original signed short-coordinate action. -/
theorem generatedSixth_xi_short_selected_operator (r s : GriessShortIndex)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s)
    (X : GriessShortIndex → ℝ) :
    localShortOperator (generatedSixthCorrectedGenerator 4) X s =
      qSign (generatedSixthXiSelectedPhase (griessShortQ r)) * X r := by
  have hc : griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r = s := by
    rw [generatedSixth_corrected_generator_spatial]
    exact hs
  rw [← hc, localShortOperator_image, generatedSixth_xi_short_selected_phase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
