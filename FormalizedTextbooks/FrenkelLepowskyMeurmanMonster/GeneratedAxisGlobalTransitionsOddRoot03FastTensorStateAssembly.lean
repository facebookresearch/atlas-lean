/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03XiInverse01Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStep02Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStep03Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03XiInverse04Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStep05Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStep06Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStep07Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStep08Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStep09Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpatialStateCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddInitialFactor

/-! Complete actual tensor source bindings for the original root-3 word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

/-- The complete initial factors are the identical actual original odd-axis tensor. -/
theorem generatedAxisGlobalOddRoot03InitialFactor :
    generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin00 generatedAxisGlobalOddRoot03Spatial00 =
      generatedAxisGlobalOddTensorInteger := by
  change generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin00
    generatedAxisGlobalOddRoot00Spatial00 = _
  exact generatedAxisGlobalOddRoot00InitialFactor

/-- Every original physical tensor coefficient is transported at actual source stage 1. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep01 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin00 generatedAxisGlobalOddRoot03Spatial00) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin01 generatedAxisGlobalOddRoot03Spatial01) 2 := by
  exact generatedAxisGlobalOddRoot03XiInverse01Tensor_actual

/-- Every original physical tensor coefficient is transported at actual source stage 2. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep02 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin01 generatedAxisGlobalOddRoot03Spatial01) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin02 generatedAxisGlobalOddRoot03Spatial02) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03SpinStep02Envelope_certificate generatedAxisGlobalOddRoot03SpatialStep02_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 3. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep03 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin02 generatedAxisGlobalOddRoot03Spatial02) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin03 generatedAxisGlobalOddRoot03Spatial03) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03SpinStep03Envelope_certificate generatedAxisGlobalOddRoot03SpatialStep03_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 4. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep04 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin03 generatedAxisGlobalOddRoot03Spatial03) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin04 generatedAxisGlobalOddRoot03Spatial04) 2 := by
  exact generatedAxisGlobalOddRoot03XiInverse04Tensor_actual

/-- Every original physical tensor coefficient is transported at actual source stage 5. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep05 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin04 generatedAxisGlobalOddRoot03Spatial04) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin05 generatedAxisGlobalOddRoot03Spatial05) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03SpinStep05Envelope_certificate generatedAxisGlobalOddRoot03SpatialStep05_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 6. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep06 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin05 generatedAxisGlobalOddRoot03Spatial05) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin06 generatedAxisGlobalOddRoot03Spatial06) 4 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 2 1 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03SpinStep06Envelope_certificate generatedAxisGlobalOddRoot03SpatialStep06_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 7. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep07 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin06 generatedAxisGlobalOddRoot03Spatial06) 4) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin07 generatedAxisGlobalOddRoot03Spatial07) 4 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 4 1 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03SpinStep07Envelope_certificate generatedAxisGlobalOddRoot03SpatialStep07_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 8. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep08 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin07 generatedAxisGlobalOddRoot03Spatial07) 4) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin08 generatedAxisGlobalOddRoot03Spatial08) 4 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    1 4 1 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03SpinStep08Envelope_certificate generatedAxisGlobalOddRoot03SpatialStep08_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 9. -/
theorem generatedAxisGlobalOddRoot03FastTensorStep09 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin08 generatedAxisGlobalOddRoot03Spatial08) 4) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin09 generatedAxisGlobalOddRoot03Spatial09) 8 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 4 2 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03SpinStep09Envelope_certificate generatedAxisGlobalOddRoot03SpatialStep09_certificate

/-- The entire final original tensor belongs to the genuine unexpanded actual source word. -/
theorem generatedAxisGlobalOddRoot03FastTensorState_actual :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3)
      generatedOddAxis)).2.2 = generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin09 generatedAxisGlobalOddRoot03Spatial09) 8 := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_tensor]
  have hw : generatedAxisGlobalOddSourceRootFiber 3 =
      (([0, 6, 9, 0, 7, 1, 6, 6, 1] : List (Fin 10)).map
        generatedAxisGlobalOddSourceFiberLetter).prod := rfl
  rw [hw, generatedAxisGlobalOddTensorInteger_packet, ← generatedAxisGlobalOddRoot03InitialFactor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    map_mul, LinearEquiv.mul_apply]
  rw [generatedAxisGlobalOddRoot03FastTensorStep01, generatedAxisGlobalOddRoot03FastTensorStep02, generatedAxisGlobalOddRoot03FastTensorStep03, generatedAxisGlobalOddRoot03FastTensorStep04, generatedAxisGlobalOddRoot03FastTensorStep05, generatedAxisGlobalOddRoot03FastTensorStep06, generatedAxisGlobalOddRoot03FastTensorStep07, generatedAxisGlobalOddRoot03FastTensorStep08, generatedAxisGlobalOddRoot03FastTensorStep09]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
