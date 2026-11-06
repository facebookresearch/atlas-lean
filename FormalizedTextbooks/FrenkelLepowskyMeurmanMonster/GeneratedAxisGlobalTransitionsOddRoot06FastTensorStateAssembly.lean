/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStep01Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStep02Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStep03Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStep04Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStep05Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStep06Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpatialStateCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06XiInverse08Certificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddInitialFactor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiExpansion

/-! Bind every complete original source tensor coordinate through normalized integer factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

/-- The complete genuine tensor transport for original source primitive 1. -/
theorem generatedAxisGlobalOddRoot06FastTensorStep01 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin00
      generatedAxisGlobalOddRoot06Spatial00) 1) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin01
      generatedAxisGlobalOddRoot06Spatial01) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 1 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot06SpinStep01Envelope_certificate
      generatedAxisGlobalOddRoot06SpatialStep01_certificate

/-- The complete genuine tensor transport for original source primitive 2. -/
theorem generatedAxisGlobalOddRoot06FastTensorStep02 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin01
      generatedAxisGlobalOddRoot06Spatial01) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin02
      generatedAxisGlobalOddRoot06Spatial02) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot06SpinStep02Envelope_certificate
      generatedAxisGlobalOddRoot06SpatialStep02_certificate

/-- The complete genuine tensor transport for original source primitive 3. -/
theorem generatedAxisGlobalOddRoot06FastTensorStep03 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin02
      generatedAxisGlobalOddRoot06Spatial02) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin03
      generatedAxisGlobalOddRoot06Spatial03) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot06SpinStep03Envelope_certificate
      generatedAxisGlobalOddRoot06SpatialStep03_certificate

/-- The complete genuine tensor transport for original source primitive 4. -/
theorem generatedAxisGlobalOddRoot06FastTensorStep04 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin03
      generatedAxisGlobalOddRoot06Spatial03) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin04
      generatedAxisGlobalOddRoot06Spatial04) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot06SpinStep04Envelope_certificate
      generatedAxisGlobalOddRoot06SpatialStep04_certificate

/-- The complete genuine tensor transport for original source primitive 5. -/
theorem generatedAxisGlobalOddRoot06FastTensorStep05 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin04
      generatedAxisGlobalOddRoot06Spatial04) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin05
      generatedAxisGlobalOddRoot06Spatial05) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot06SpinStep05Envelope_certificate
      generatedAxisGlobalOddRoot06SpatialStep05_certificate

/-- The complete genuine tensor transport for original source primitive 6. -/
theorem generatedAxisGlobalOddRoot06FastTensorStep06 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin05
      generatedAxisGlobalOddRoot06Spatial05) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin06
      generatedAxisGlobalOddRoot06Spatial06) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot06SpinStep06Envelope_certificate
      generatedAxisGlobalOddRoot06SpatialStep06_certificate

/-- The original inverse middle letter is exactly the two already certified positive source actions. -/
theorem generatedAxisGlobalOddRoot06FastTensorInverseMiddle :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin03
          generatedAxisGlobalOddRoot06Spatial03) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin05
        generatedAxisGlobalOddRoot06Spatial05) 2 := by
  rw [generatedAxisGlobalOddSourceFiberLetter_one, map_mul]
  rw [LinearEquiv.mul_apply, generatedAxisGlobalOddRoot06FastTensorStep04,
    generatedAxisGlobalOddRoot06FastTensorStep05]

/-- Every physical tensor coordinate is the stated complete packet for the actual source word. -/
theorem generatedAxisGlobalOddRoot06FastTensorState_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis)).2.2 =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin08
      generatedAxisGlobalOddRoot06Spatial08) 2 := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_tensor]
  have hw : generatedAxisGlobalOddSourceRootFiber 6 =
      (([1,9,1,7,7,0] : List (Fin 10)).map
        generatedAxisGlobalOddSourceFiberLetter).prod := rfl
  rw [hw]
  rw [generatedAxisGlobalOddTensorInteger_packet, ← generatedAxisGlobalOddRoot06InitialFactor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    map_mul, LinearEquiv.mul_apply]
  rw [generatedAxisGlobalOddRoot06FastTensorStep01,
    generatedAxisGlobalOddRoot06FastTensorStep02,
    generatedAxisGlobalOddRoot06FastTensorStep03,
    generatedAxisGlobalOddRoot06FastTensorInverseMiddle,
    generatedAxisGlobalOddRoot06FastTensorStep06,
    generatedAxisGlobalOddRoot06XiInverse08Tensor_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
