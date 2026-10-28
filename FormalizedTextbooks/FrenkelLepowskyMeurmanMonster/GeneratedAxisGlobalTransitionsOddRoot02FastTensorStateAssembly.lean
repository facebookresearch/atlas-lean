/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep01Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep02Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep03Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep04Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep05Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep06Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep07Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02XiInverse08Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep09Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStep10Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02XiInverse11Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpatialStateCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddInitialFactor

/-! Complete actual tensor source bindings for the original root-2 word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

/-- The complete initial factors are the identical actual original odd-axis tensor. -/
theorem generatedAxisGlobalOddRoot02InitialFactor :
    generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin00 generatedAxisGlobalOddRoot02Spatial00 =
      generatedAxisGlobalOddTensorInteger := by
  change generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin00
    generatedAxisGlobalOddRoot00Spatial00 = _
  exact generatedAxisGlobalOddRoot00InitialFactor

/-- Every original physical tensor coefficient is transported at actual source stage 1. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep01 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin00 generatedAxisGlobalOddRoot02Spatial00) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin01 generatedAxisGlobalOddRoot02Spatial01) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep01Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep01_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 2. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep02 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin01 generatedAxisGlobalOddRoot02Spatial01) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin02 generatedAxisGlobalOddRoot02Spatial02) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep02Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep02_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 3. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep03 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin02 generatedAxisGlobalOddRoot02Spatial02) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin03 generatedAxisGlobalOddRoot02Spatial03) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep03Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep03_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 4. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep04 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin03 generatedAxisGlobalOddRoot02Spatial03) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin04 generatedAxisGlobalOddRoot02Spatial04) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 1 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep04Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep04_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 5. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep05 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin04 generatedAxisGlobalOddRoot02Spatial04) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin05 generatedAxisGlobalOddRoot02Spatial05) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep05Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep05_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 6. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep06 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin05 generatedAxisGlobalOddRoot02Spatial05) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin06 generatedAxisGlobalOddRoot02Spatial06) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep06Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep06_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 7. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep07 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin06 generatedAxisGlobalOddRoot02Spatial06) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin07 generatedAxisGlobalOddRoot02Spatial07) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep07Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep07_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 8. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep08 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin07 generatedAxisGlobalOddRoot02Spatial07) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin08 generatedAxisGlobalOddRoot02Spatial08) 4 := by
  exact generatedAxisGlobalOddRoot02XiInverse08Tensor_actual

/-- Every original physical tensor coefficient is transported at actual source stage 9. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep09 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin08 generatedAxisGlobalOddRoot02Spatial08) 4) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin09 generatedAxisGlobalOddRoot02Spatial09) 4 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 4 1 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep09Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep09_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 10. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep10 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin09 generatedAxisGlobalOddRoot02Spatial09) 4) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin10 generatedAxisGlobalOddRoot02Spatial10) 4 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 4 1 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02SpinStep10Envelope_certificate generatedAxisGlobalOddRoot02SpatialStep10_certificate

/-- Every original physical tensor coefficient is transported at actual source stage 11. -/
theorem generatedAxisGlobalOddRoot02FastTensorStep11 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin10 generatedAxisGlobalOddRoot02Spatial10) 4) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin11 generatedAxisGlobalOddRoot02Spatial11) 8 := by
  exact generatedAxisGlobalOddRoot02XiInverse11Tensor_actual

/-- The entire final original tensor belongs to the genuine unexpanded actual source word. -/
theorem generatedAxisGlobalOddRoot02FastTensorState_actual :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2)
      generatedOddAxis)).2.2 = generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin11 generatedAxisGlobalOddRoot02Spatial11) 8 := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_tensor]
  have hw : generatedAxisGlobalOddSourceRootFiber 2 =
      (([1, 7, 9, 1, 7, 9, 6, 0, 9, 6, 9] : List (Fin 10)).map
        generatedAxisGlobalOddSourceFiberLetter).prod := rfl
  rw [hw, generatedAxisGlobalOddTensorInteger_packet, ← generatedAxisGlobalOddRoot02InitialFactor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    map_mul, LinearEquiv.mul_apply]
  rw [generatedAxisGlobalOddRoot02FastTensorStep01, generatedAxisGlobalOddRoot02FastTensorStep02, generatedAxisGlobalOddRoot02FastTensorStep03, generatedAxisGlobalOddRoot02FastTensorStep04, generatedAxisGlobalOddRoot02FastTensorStep05, generatedAxisGlobalOddRoot02FastTensorStep06, generatedAxisGlobalOddRoot02FastTensorStep07, generatedAxisGlobalOddRoot02FastTensorStep08, generatedAxisGlobalOddRoot02FastTensorStep09, generatedAxisGlobalOddRoot02FastTensorStep10, generatedAxisGlobalOddRoot02FastTensorStep11]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
