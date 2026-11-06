/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortWeights
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneSpinCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMiddleTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityKleinFour

/-! A normalized complete middle axis, retaining the two possible genuine spin signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- The canonical middle triple has the actual matrix and short blocks and the checked spin sign. -/
def generatedSeventhXiPlaneCanonicalMiddleRaw : ConwayRawSpace :=
  ((griessConwayEncode
    (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).1,
   ((griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1,
    fun t j => -generatedSeventhXiPlaneNormalizedSpin t *
      (generatedSeventhFrameVectorData 7 0 j : ℝ) / Real.sqrt 2))

/-- This complete middle vector is decoded from its symmetric Conway matrix. -/
def generatedSeventhXiPlaneCanonicalMiddle : GriessSpace :=
  griessConwayDecode generatedSeventhXiPlaneCanonicalMiddleRaw

/-- Encoding recovers every canonical middle coordinate without any projection. -/
theorem generatedSeventhXiPlaneCanonicalMiddle_encode :
    griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle =
      generatedSeventhXiPlaneCanonicalMiddleRaw := by
  apply griessConwayEncode_decode
  exact griessConwayEncode_symmetric _

/-- The genuine middle tensor has its exact spatial integer numerator and spin normalization. -/
theorem generatedSeventhXi_middle_tensor_normalized (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.2 t j =
      -generatedSeventhSpinState t *
        (generatedSeventhFrameVectorData 7 0 j : ℝ) / Real.sqrt 2 := by
  rw [generatedSeventh_middle_tensor_rank_one]
  have hv : generatedSeventhLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) j =
      (generatedSeventhFrameVectorData 7 0 j : ℝ) / 8 :=
    generatedSeventh_forward_matrix_coordinate j 0
  rw [hv]
  change (-8 / Real.sqrt 2) * generatedSeventhSpinState t *
    ((generatedSeventhFrameVectorData 7 0 j : ℝ) / 8) = _
  ring

/-- The entire middle axis equals the canonical one or its actual central involution image. -/
theorem generatedSeventhXi_middle_canonical_sign :
    rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis =
      generatedSeventhXiPlaneCanonicalMiddle ∨
    rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis =
      localCentralGriess generatedSeventhXiPlaneCanonicalMiddle := by
  rcases generatedSeventhXiPlane_spin_normalized_sign with hs | hs
  · left
    have he : griessConwayEncode
        (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis) =
        griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle := by
      rw [generatedSeventhXiPlaneCanonicalMiddle_encode]
      refine Prod.ext (by rfl) ?_
      refine Prod.ext (by rfl) ?_
      funext t j
      rw [generatedSeventhXi_middle_tensor_normalized, hs]
      rfl
    have hd := congrArg griessConwayDecode he
    simpa only [griessConwayDecode_encode] using hd
  · right
    have he : griessConwayEncode
        (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis) =
        griessConwayEncode (localCentralGriess generatedSeventhXiPlaneCanonicalMiddle) := by
      rw [localCentralGriess_encode, generatedSeventhXiPlaneCanonicalMiddle_encode]
      refine Prod.ext (by rfl) ?_
      refine Prod.ext (by rfl) ?_
      funext t j
      rw [generatedSeventhXi_middle_tensor_normalized, hs]
      change -(-generatedSeventhXiPlaneNormalizedSpin t) *
          (generatedSeventhFrameVectorData 7 0 j : ℝ) / Real.sqrt 2 =
        -(-generatedSeventhXiPlaneNormalizedSpin t *
          (generatedSeventhFrameVectorData 7 0 j : ℝ) / Real.sqrt 2)
      ring
    have hd := congrArg griessConwayDecode he
    simpa only [griessConwayDecode_encode] using hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
