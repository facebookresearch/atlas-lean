/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortMaskPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSelectedMaskPhase

/-! Exact scalar XOR evaluates the original Ninth preferred-Q phase, retaining the source
ordered-section correction and every genuine coordinate-image central coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Packed cocycle rows of the original positive hyperbolic coordinate generators. -/
def generatedNinthCompactInputPairRows (i : Fin 24) : ℕ :=
  if i.val < 12 then 1 <<< (i.val + 12) else 0

/-- Every packed input bit is the original coordinate-generator cocycle pairing. -/
theorem generatedNinth_compact_input_pair_rows : ∀ i j : Fin 24,
    (if (generatedNinthCompactInputPairRows i).testBit j.val then (1 : ZMod 2) else 0) =
      monsterNortonCoordinatePairPhase i j := by
  decide +kernel

/-- Complete central coefficients of the24 checked original Ninth coordinate images. -/
def generatedNinthCompactCoordinateCentralMask : ℕ := 11040867

/-- Every packed scalar bit is the full central coefficient of its actual original image. -/
theorem generatedNinth_compact_coordinate_central_mask : ∀ i : Fin 24,
    (if generatedNinthCompactCoordinateCentralMask.testBit i.val then (1 : ZMod 2) else 0) =
      (generatedNinthCoordinateImageLabels i).2.2 := by
  decide +kernel

/-- Full original preferred-Q phase evaluated by characteristic-two scalar XOR. -/
def generatedNinthShortRowCompactPhase (n : ℕ) : ZMod 2 :=
  generatedSixthXiMaskParity (Nat.xor
    (generatedSixthXiSelectedMaskPhase 0 generatedNinthCompactInputPairRows n (List.finRange 24))
    (generatedSixthXiSelectedMaskPhase generatedNinthCompactCoordinateCentralMask
      generatedNinthCoordinatePairMasks n (List.finRange 24)))

/-- The scalar XOR formula equals the actual full original preferred-Q phase for every mask. -/
theorem generatedNinth_mask_preferred_compact_phase (n : ℕ) :
    generatedNinthMaskPreferredPhase n = generatedNinthShortRowCompactPhase n := by
  have hp : (fun i j => if (generatedNinthCompactInputPairRows i).testBit j.val then
      (1 : ZMod 2) else 0) = monsterNortonCoordinatePairPhase := by
    funext i j
    exact generatedNinth_compact_input_pair_rows i j
  have hc : (fun i : Fin 24 => if generatedNinthCompactCoordinateCentralMask.testBit i.val then
      (1 : ZMod 2) else 0) = (fun i => (generatedNinthCoordinateImageLabels i).2.2) := by
    funext i
    exact generatedNinth_compact_coordinate_central_mask i
  rw [generatedNinthShortRowCompactPhase, generatedSixth_xi_mask_parity_xor,
    generatedSixth_xi_selected_mask_phase, generatedSixth_xi_selected_mask_phase, hp, hc]
  change (0 : ZMod 2) + _ + _ = _
  rw [zero_add]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
