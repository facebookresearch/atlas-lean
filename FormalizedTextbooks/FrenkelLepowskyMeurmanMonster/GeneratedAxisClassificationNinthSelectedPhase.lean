/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQCoordinateEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQSelectedPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSelectedPhase

/-! Scalar pairings evaluate the literal ninth spin word's full central phase. Every nonzero
coordinate-image correction and the original ordered-section correction are retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Packed actual cocycle pairings of all twenty-four original ninth coordinate images. -/
def generatedNinthCoordinatePairMasks : Fin 24 → ℕ :=
  ![4482594, 4560545, 16010816, 16157824, 5639648, 2688467,
    7666356, 2594938, 14013488, 6348871, 4063551, 11206876,
    6054339, 6197827, 5280577, 5333954, 4491698, 10235064,
    2831775, 5651616, 2815068, 5508332, 2750303, 131340]

/-- A scalar pairing bit, in the genuine original cocycle orientation. -/
def generatedNinthCoordinatePairPhase (i j : Fin 24) : ZMod 2 :=
  if (generatedNinthCoordinatePairMasks i).testBit j.val then 1 else 0

set_option maxHeartbeats 16000000 in
-- Check all576 scalar bits against the actual full original coordinate images.
/-- Every scalar bit equals the cocycle pairing of the checked original Q images. -/
theorem generatedNinth_coordinate_pair_phase_actual (i j : Fin 24) :
    qBeta (toAdd (generatedNinthCoordinateImage i).base)
      (toAdd (generatedNinthCoordinateImage j).base) =
        generatedNinthCoordinatePairPhase i j := by
  revert i j
  decide +kernel

/-- The complete ninth central phase without forming actual Q products. -/
def generatedNinthSelectedPhase (q : Q) : ZMod 2 :=
  toAdd q.coeff + generatedSixthQSelectedPhase (fun _ => 0)
    monsterNortonCoordinatePairPhase (toAdd q.base) (List.finRange 24) +
    generatedSixthQSelectedPhase
      (fun i => (generatedNinthCoordinateImageLabels i).2.2)
      generatedNinthCoordinatePairPhase (toAdd q.base) (List.finRange 24)

/-- The scalar expression is the exact original nine-factor automorphism's central coefficient. -/
theorem generatedNinth_selected_phase (q : Q) :
    toAdd (generatedNinthQImage q).coeff = generatedNinthSelectedPhase q := by
  rw [generatedNinth_QCoordinateEvaluation_eq]
  rw [generatedNinthQCoordinateEvaluation, monsterNortonCoordinateEvaluation_finite_phase,
    List.ofFn_eq_map, List.ofFn_eq_map]
  rw [generatedSixth_Q_selected_phase_actual _ _ _ (fun _ => rfl)
    monsterNortonCoordinatePairPhase_actual]
  rw [generatedSixth_Q_selected_phase_actual _ _ _ (fun _ => rfl)
    generatedNinth_coordinate_pair_phase_actual]
  rfl

/-- The original preferred-short phase is evaluated on the genuine source Q lift. -/
theorem generatedNinth_short_selected_phase (r : GriessShortIndex) :
    localShortPhase generatedNinthLocalFiber r = generatedNinthSelectedPhase (griessShortQ r) := by
  simpa only [localShortPhase, generatedNinthQImage_eq] using
    generatedNinth_selected_phase (griessShortQ r)

/-- A recognized actual spatial image gives the complete signed short-coordinate action. -/
theorem generatedNinth_short_selected_operator (r s : GriessShortIndex)
    (hs : griessShortPermutation generatedNinthLocalFiber.val.2 r = s)
    (X : GriessShortIndex → ℝ) :
    localShortOperator generatedNinthLocalFiber X s =
      qSign (generatedNinthSelectedPhase (griessShortQ r)) * X r := by
  rw [← hs, localShortOperator_image, generatedNinth_short_selected_phase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
