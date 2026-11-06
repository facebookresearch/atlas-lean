/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01CorrectionEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00FastTensorStateAssembly

/-! Complete tensor constituent of the actual original local comparison word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire tensor packet follows from the original root and both full correction factors. -/
theorem generatedAxisGlobalOddComparison01FastTensor_packet :
    localTensorRepresentation (generatedAxisGlobalOddComparisonFiber 1)
        ((griessConwayEncode generatedOddAxis).2.2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddComparison01Spin
          generatedAxisGlobalOddComparison01Spatial) 8 := by
  have ht := generatedAxisGlobalOddRoot00FastTensorState_actual
  rw [generatedAxisGlobalOddSourceRootFiber_encode,
    localConwayRawRepresentation_tensor] at ht
  have h := generatedAxisGlobalOddComparisonTensor_of_root_packet 1
    generatedAxisGlobalOddRoot00Spin12
    generatedAxisGlobalOddRoot00Spatial12 4 ht
  have hs : generatedAxisGlobalOddComparisonSpinInteger 1
      generatedAxisGlobalOddRoot00Spin12 =
        generatedAxisGlobalOddComparison01Spin :=
    funext generatedAxisGlobalOddComparison01EnvelopeSpin_certificate
  have hv : generatedAxisGlobalOddComparisonSpatialInteger 1
      generatedAxisGlobalOddRoot00Spatial12 =
        generatedAxisGlobalOddComparison01Spatial :=
    funext generatedAxisGlobalOddComparison01EnvelopeSpatial_certificate
  rw [hs, hv] at h
  exact h

/-- Every physical tensor coordinate belongs to the literal complete actual local word. -/
theorem generatedAxisGlobalOddComparison01FastTensor_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal 1) generatedOddAxis)).2.2 =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddComparison01Spin
          generatedAxisGlobalOddComparison01Spatial) 8 := by
  have he : griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddComparisonLocal 1) generatedOddAxis) =
      localConwayRawRepresentation (generatedAxisGlobalOddComparisonFiber 1)
        (griessConwayEncode generatedOddAxis) := by
    rw [← generatedAxisGlobalOddComparisonFiber_local]
    exact localGriessRepresentation_encode _ _
  rw [he, localConwayRawRepresentation_tensor]
  exact generatedAxisGlobalOddComparison01FastTensor_packet

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
