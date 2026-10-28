/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingDestination
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorColumns

/-! Eight genuine source factors give the entire actual compact incoming tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The complete original spin column with its genuine square-root normalization. -/
def generatedRootEightIncomingTensorSourceSpin (r : Fin 8) : SpinSpace :=
  fun t => (generatedTwelfthTensorSourceSpin r (generatedAxisGlobalSpinLabel t) : ℝ) / Real.sqrt 2

/-- The genuine original physical source unit vector, embedded over the reals. -/
def generatedRootEightIncomingTensorSourceSpatial (r : Fin 8) : Fin 24 → ℝ :=
  fun i => (generatedTwelfthTensorSourceSpatial r i : ℝ)

/-- One complete physical source column equals its actual pure tensor. -/
theorem generatedRootEight_incoming_tensor_source_factor (r : Fin 8) :
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor (generatedTwelfthTensorSourceSpin r)
        (generatedTwelfthTensorSourceSpatial r)) 1 =
      conwayTensorCoordinates (generatedRootEightIncomingTensorSourceSpin r ⊗ₜ[ℝ]
        generatedRootEightIncomingTensorSourceSpatial r) := by
  ext t i
  simp only [generatedAxisGlobalTensorIntegerPacket, generatedAxisGlobalOddTensorFactor,
    Nat.cast_one, one_mul, Int.cast_mul, conwayTensorCoordinates_tmul,
    generatedRootEightIncomingTensorSourceSpin, generatedRootEightIncomingTensorSourceSpatial]
  ring

/-- Each complete incoming spin factor is acted on by the actual compact spin normalizer. -/
def generatedRootEightIncomingTensorSpin (r : Fin 8) : SpinSpace :=
  (generatedRootEightIncomingCompactSpin 0).val (generatedRootEightIncomingTensorSourceSpin r)

/-- Each physical factor follows the literal original word-eight spatial isometry. -/
def generatedRootEightIncomingTensorSpatial (r : Fin 8) : Fin 24 → ℝ :=
  (generatedTenthQWordFiber 8).val.2.val (generatedRootEightIncomingTensorSourceSpatial r)

/-- The whole incoming physical factor retains its full spin and spatial coordinates. -/
def generatedRootEightIncomingTensorFactor (r : Fin 8) : SpinIndex → Fin 24 → ℝ :=
  conwayTensorCoordinates (generatedRootEightIncomingTensorSpin r ⊗ₜ[ℝ]
    generatedRootEightIncomingTensorSpatial r)

/-- Every source factor is transported by the genuine defining tensor action. -/
theorem generatedRootEight_incoming_tensor_factor_action (r : Fin 8) :
    localTensorRepresentation generatedRootEightIncomingCertifiedFiber
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (generatedTwelfthTensorSourceSpin r)
          (generatedTwelfthTensorSourceSpatial r)) 1) =
      generatedRootEightIncomingTensorFactor r := by
  rw [generatedRootEight_incoming_tensor_source_factor, generatedAxisGlobalTensor_local_tmul]
  rfl

/-- All physical tensor entries equal the sum of the eight genuinely transported source factors. -/
theorem generatedRootEight_incoming_tensor_factors :
    (griessConwayEncode generatedRootEightIncomingDestination).2.2 =
      ∑ r : Fin 8, generatedRootEightIncomingTensorFactor r := by
  change (griessConwayEncode (localGriessRepresentation generatedRootEightIncomingCertifiedFiber
    generatedFifthAxis)).2.2 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor,
    generatedTwelfth_tensor_source_actual, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact generatedRootEight_incoming_tensor_factor_action r

/-- Every actual incoming tensor coordinate is the complete eight-factor spin/spatial sum. -/
theorem generatedRootEight_incoming_tensor_coordinate (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedRootEightIncomingDestination).2.2 t i =
      ∑ r : Fin 8, generatedRootEightIncomingTensorSpin r t *
        generatedRootEightIncomingTensorSpatial r i := by
  rw [generatedRootEight_incoming_tensor_factors]
  simp only [Finset.sum_apply, generatedRootEightIncomingTensorFactor, conwayTensorCoordinates_tmul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
