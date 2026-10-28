/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSelectedMaskPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiMaskCoordinates

/-! The full original Xi phase is evaluated by exact scalar XOR with certified central bits. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Packed cocycle pairings of the original positive hyperbolic coordinate generators. -/
def generatedSixthXiInputPairRows (i : Fin 24) : ℕ :=
  if i.val < 12 then 1 <<< (i.val + 12) else 0

/-- Full genuine central coefficients of all 24 checked corrected-Xi generator images. -/
def generatedSixthXiCoordinateCentralMask : ℕ := 5195609

/-- Every original pairing bit has the genuine input-cocycle orientation. -/
theorem generatedSixth_xi_input_pair_rows : ∀ i j : Fin 24,
    (if (generatedSixthXiInputPairRows i).testBit j.val then (1 : ZMod 2) else 0) =
      monsterNortonCoordinatePairPhase i j := by
  decide +kernel

/-- All packed central bits are the complete coefficients of the checked original images. -/
theorem generatedSixth_xi_coordinate_central_mask : ∀ i : Fin 24,
    (if generatedSixthXiCoordinateCentralMask.testBit i.val then (1 : ZMod 2) else 0) =
      (generatedSixthXiCoordinateImageLabels i).2.2 := by
  decide +kernel

/-- Complete corrected-Xi phase, retaining the source normal form and every image central bit. -/
def generatedSixthXiFastMaskPhase (n : ℕ) : ZMod 2 :=
  generatedSixthXiMaskParity (Nat.xor
    (generatedSixthXiSelectedMaskPhase 0 generatedSixthXiInputPairRows n (List.finRange 24))
    (generatedSixthXiSelectedMaskPhase generatedSixthXiCoordinateCentralMask
      generatedSixthXiCoordinatePairMasks n (List.finRange 24)))

/-- Exact bit arithmetic equals the previously proved entire original Xi scalar phase. -/
theorem generatedSixth_xi_fast_mask_phase (n : ℕ) :
    generatedSixthXiSelectedPhase (generatedSixthXiMaskQ n) =
      generatedSixthXiFastMaskPhase n := by
  have hp : (fun i j => if (generatedSixthXiInputPairRows i).testBit j.val then
      (1 : ZMod 2) else 0) = monsterNortonCoordinatePairPhase := by
    funext i j
    exact generatedSixth_xi_input_pair_rows i j
  have hc : (fun i : Fin 24 => if generatedSixthXiCoordinateCentralMask.testBit i.val then
      (1 : ZMod 2) else 0) = (fun i => (generatedSixthXiCoordinateImageLabels i).2.2) := by
    funext i
    exact generatedSixth_xi_coordinate_central_mask i
  rw [generatedSixthXiFastMaskPhase, generatedSixth_xi_mask_parity_xor,
    generatedSixth_xi_selected_mask_phase, generatedSixth_xi_selected_mask_phase, hp, hc]
  change (0 : ZMod 2) + _ + _ = _
  rw [zero_add]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
