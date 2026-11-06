/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02CorrectionEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06FastTensorStateAssembly

/-! Complete tensor constituent of the actual original local comparison word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire tensor packet follows from the original root and both full correction factors. -/
theorem generatedAxisGlobalOddComparison02FastTensor_packet :
    localTensorRepresentation (generatedAxisGlobalOddComparisonFiber 2)
        ((griessConwayEncode generatedOddAxis).2.2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddComparison02Spin
          generatedAxisGlobalOddComparison02Spatial) 4 := by
  have ht := generatedAxisGlobalOddRoot06FastTensorState_actual
  rw [generatedAxisGlobalOddSourceRootFiber_encode,
    localConwayRawRepresentation_tensor] at ht
  have h := generatedAxisGlobalOddComparisonTensor_of_root_packet 2
    generatedAxisGlobalOddRoot06Spin08
    generatedAxisGlobalOddRoot06Spatial08 2 ht
  have hs : generatedAxisGlobalOddComparisonSpinInteger 2
      generatedAxisGlobalOddRoot06Spin08 =
        generatedAxisGlobalOddComparison02Spin :=
    funext generatedAxisGlobalOddComparison02EnvelopeSpin_certificate
  have hv : generatedAxisGlobalOddComparisonSpatialInteger 2
      generatedAxisGlobalOddRoot06Spatial08 =
        generatedAxisGlobalOddComparison02Spatial :=
    funext generatedAxisGlobalOddComparison02EnvelopeSpatial_certificate
  rw [hs, hv] at h
  exact h

/-- Every physical tensor coordinate belongs to the literal complete actual local word. -/
theorem generatedAxisGlobalOddComparison02FastTensor_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal 2) generatedOddAxis)).2.2 =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddComparison02Spin
          generatedAxisGlobalOddComparison02Spatial) 4 := by
  have he : griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal 2) generatedOddAxis) =
      localConwayRawRepresentation (generatedAxisGlobalOddComparisonFiber 2)
        (griessConwayEncode generatedOddAxis) := by
    rw [← generatedAxisGlobalOddComparisonFiber_local]
    exact localGriessRepresentation_encode _ _
  rw [he, localConwayRawRepresentation_tensor]
  exact generatedAxisGlobalOddComparison02FastTensor_packet

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
