/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep01Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep02Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep03Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep04Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep05Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep06Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep07Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStep08Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpatialStateCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04XiInverseFinalCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddInitialFactor

/-! Complete actual tensor source bindings for the original root-four word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

/-- The exact initial factors are the original odd-axis tensor packet. -/
theorem generatedAxisGlobalOddRoot04InitialFactor :
    generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin00 generatedAxisGlobalOddRoot04Spatial00 =
      generatedAxisGlobalOddTensorInteger := by
  change generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin00
    generatedAxisGlobalOddRoot00Spatial00 = _
  exact generatedAxisGlobalOddRoot00InitialFactor

/-- Every physical original tensor coefficient is transported at stage 1. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep01 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin00 generatedAxisGlobalOddRoot04Spatial00) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin01 generatedAxisGlobalOddRoot04Spatial01) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep01Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep01_certificate

/-- Every physical original tensor coefficient is transported at stage 2. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep02 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 3)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin01 generatedAxisGlobalOddRoot04Spatial01) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin02 generatedAxisGlobalOddRoot04Spatial02) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 3 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep02Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep02_certificate

/-- Every physical original tensor coefficient is transported at stage 3. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep03 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin02 generatedAxisGlobalOddRoot04Spatial02) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin03 generatedAxisGlobalOddRoot04Spatial03) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep03Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep03_certificate

/-- Every physical original tensor coefficient is transported at stage 4. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep04 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin03 generatedAxisGlobalOddRoot04Spatial03) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin04 generatedAxisGlobalOddRoot04Spatial04) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep04Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep04_certificate

/-- Every physical original tensor coefficient is transported at stage 5. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep05 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin04 generatedAxisGlobalOddRoot04Spatial04) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin05 generatedAxisGlobalOddRoot04Spatial05) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep05Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep05_certificate

/-- Every physical original tensor coefficient is transported at stage 6. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep06 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 3)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin05 generatedAxisGlobalOddRoot04Spatial05) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin06 generatedAxisGlobalOddRoot04Spatial06) 1 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 3 _ _ _ _
    1 1 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep06Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep06_certificate

/-- Every physical original tensor coefficient is transported at stage 7. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep07 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin06 generatedAxisGlobalOddRoot04Spatial06) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin07 generatedAxisGlobalOddRoot04Spatial07) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 1 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep07Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep07_certificate

/-- Every physical original tensor coefficient is transported at stage 8. -/
theorem generatedAxisGlobalOddRoot04FastTensorStep08 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin07 generatedAxisGlobalOddRoot04Spatial07) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin08 generatedAxisGlobalOddRoot04Spatial08) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot04SpinStep08Envelope_certificate generatedAxisGlobalOddRoot04SpatialStep08_certificate

/-- The entire final original tensor belongs to the genuine unexpanded source word. -/
theorem generatedAxisGlobalOddRoot04FastTensorState_actual :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4)
      generatedOddAxis)).2.2 = generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot04Spin09 generatedAxisGlobalOddRoot04Spatial09) 4 := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_tensor]
  have hw : generatedAxisGlobalOddSourceRootFiber 4 =
      (([1, 9, 0, 3, 6, 9, 7, 3, 7] : List (Fin 10)).map
        generatedAxisGlobalOddSourceFiberLetter).prod := rfl
  rw [hw, generatedAxisGlobalOddTensorInteger_packet, ← generatedAxisGlobalOddRoot04InitialFactor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    map_mul, LinearEquiv.mul_apply]
  rw [generatedAxisGlobalOddRoot04FastTensorStep01, generatedAxisGlobalOddRoot04FastTensorStep02, generatedAxisGlobalOddRoot04FastTensorStep03, generatedAxisGlobalOddRoot04FastTensorStep04, generatedAxisGlobalOddRoot04FastTensorStep05, generatedAxisGlobalOddRoot04FastTensorStep06, generatedAxisGlobalOddRoot04FastTensorStep07, generatedAxisGlobalOddRoot04FastTensorStep08,
    generatedAxisGlobalOddRoot04XiInverseFinalTensor_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
