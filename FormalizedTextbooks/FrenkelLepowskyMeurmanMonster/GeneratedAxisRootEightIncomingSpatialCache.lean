/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingSpatialAction

/-! Eight genuine spin and positive physical factors give the complete incoming tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Each physical factor follows the explicit positive original incoming isometry. -/
def generatedRootEightIncomingPositiveTensorSpatial (r : Fin 8) : Fin 24 → ℝ :=
  (generatedAxisGlobalFifthShortSpatialWord 8).val (generatedRootEightIncomingTensorSourceSpatial r)

/-- All eight complete incoming positive physical vectors have their exact rational coordinates. -/
theorem generatedRootEight_incoming_positive_tensor_spatial (r : Fin 8) (i : Fin 24) :
    generatedRootEightIncomingPositiveTensorSpatial r i =
      (generatedRootEightIncomingSpatialNumerator r i : ℝ) / 4 := by
  have hs : generatedRootEightIncomingTensorSourceSpatial r =
      Pi.single (generatedTwelfthTensorSourceCoordinate r) (1 : ℝ) := by
    ext j
    by_cases hj : j = generatedTwelfthTensorSourceCoordinate r <;>
      simp [generatedRootEightIncomingTensorSourceSpatial, generatedTwelfthTensorSourceSpatial, hj]
  rw [generatedRootEightIncomingPositiveTensorSpatial, hs]
  exact generatedRootEight_incoming_positive_spatial_unit r i

/-- A complete incoming factor retains the actual compact spin and positive physical coordinates. -/
def generatedRootEightIncomingPositiveTensorFactor (r : Fin 8) : SpinIndex → Fin 24 → ℝ :=
  conwayTensorCoordinates (generatedRootEightIncomingTensorSpin r ⊗ₜ[ℝ]
    generatedRootEightIncomingPositiveTensorSpatial r)

/-- Every original source factor is carried by the genuine defining positive tensor action. -/
theorem generatedRootEight_incoming_positive_tensor_factor_action (r : Fin 8) :
    localTensorRepresentation generatedRootEightIncomingPositiveFiber
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (generatedTwelfthTensorSourceSpin r)
          (generatedTwelfthTensorSourceSpatial r)) 1) =
      generatedRootEightIncomingPositiveTensorFactor r := by
  rw [generatedRootEight_incoming_tensor_source_factor, generatedAxisGlobalTensor_local_tmul]
  rfl

/-- Every actual positive incoming tensor entry is the sum of the eight genuine source factors. -/
theorem generatedRootEight_incoming_positive_tensor_factors :
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).2.2 =
      ∑ r : Fin 8, generatedRootEightIncomingPositiveTensorFactor r := by
  change (griessConwayEncode (localGriessRepresentation generatedRootEightIncomingPositiveFiber
    generatedFifthAxis)).2.2 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor,
    generatedTwelfth_tensor_source_actual, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact generatedRootEight_incoming_positive_tensor_factor_action r

/-- The whole actual incoming tensor has its exact eight-column spin and rational physical formula. -/
theorem generatedRootEight_incoming_positive_tensor_coordinate (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).2.2 t i =
      ∑ r : Fin 8, generatedRootEightIncomingTensorSpin r t *
        ((generatedRootEightIncomingSpatialNumerator r i : ℝ) / 4) := by
  rw [generatedRootEight_incoming_positive_tensor_factors]
  simp only [Finset.sum_apply, generatedRootEightIncomingPositiveTensorFactor,
    conwayTensorCoordinates_tmul, generatedRootEight_incoming_positive_tensor_spatial]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
