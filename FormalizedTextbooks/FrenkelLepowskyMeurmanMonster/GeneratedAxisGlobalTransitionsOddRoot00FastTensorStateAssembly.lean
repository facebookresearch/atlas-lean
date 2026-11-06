/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep07Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep08Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep09Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep10Envelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpatialStateCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00XiInverseFinalCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddInitialFactor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiExpansion

/-! Bind every complete original source tensor coordinate through normalized integer factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

/-- The complete genuine tensor transport for original source primitive 1. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep01 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin00
      generatedAxisGlobalOddRoot00Spatial00) 1) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin01
      generatedAxisGlobalOddRoot00Spatial01) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 1 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep01_certificate
      generatedAxisGlobalOddRoot00SpatialStep01_certificate

/-- The complete genuine tensor transport for original source primitive 2. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep02 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin01
      generatedAxisGlobalOddRoot00Spatial01) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin02
      generatedAxisGlobalOddRoot00Spatial02) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep02_certificate
      generatedAxisGlobalOddRoot00SpatialStep02_certificate

/-- The complete genuine tensor transport for original source primitive 3. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep03 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin02
      generatedAxisGlobalOddRoot00Spatial02) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin03
      generatedAxisGlobalOddRoot00Spatial03) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep03_certificate
      generatedAxisGlobalOddRoot00SpatialStep03_certificate

/-- The complete genuine tensor transport for original source primitive 4. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep04 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin03
      generatedAxisGlobalOddRoot00Spatial03) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin04
      generatedAxisGlobalOddRoot00Spatial04) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep04_certificate
      generatedAxisGlobalOddRoot00SpatialStep04_certificate

/-- The complete genuine tensor transport for original source primitive 5. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep05 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 7)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin04
      generatedAxisGlobalOddRoot00Spatial04) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin05
      generatedAxisGlobalOddRoot00Spatial05) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 7 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep05_certificate
      generatedAxisGlobalOddRoot00SpatialStep05_certificate

/-- The complete genuine tensor transport for original source primitive 6. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep06 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 9)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin05
      generatedAxisGlobalOddRoot00Spatial05) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin06
      generatedAxisGlobalOddRoot00Spatial06) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 9 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep06_certificate
      generatedAxisGlobalOddRoot00SpatialStep06_certificate

/-- The complete genuine tensor transport for original source primitive 7. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep07 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 5)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin06
      generatedAxisGlobalOddRoot00Spatial06) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin07
      generatedAxisGlobalOddRoot00Spatial07) 2 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 5 _ _ _ _
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep07Envelope_certificate
      generatedAxisGlobalOddRoot00SpatialStep07_certificate

/-- The complete genuine tensor transport for original source primitive 8. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep08 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 0)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin07
      generatedAxisGlobalOddRoot00Spatial07) 2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin08
      generatedAxisGlobalOddRoot00Spatial08) 8 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 0 _ _ _ _
    1 2 2 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep08Envelope_certificate
      generatedAxisGlobalOddRoot00SpatialStep08_certificate

/-- The complete genuine tensor transport for original source primitive 9. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep09 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin08
      generatedAxisGlobalOddRoot00Spatial08) 8) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin09
      generatedAxisGlobalOddRoot00Spatial09) 8 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    2 4 2 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep09Envelope_certificate
      generatedAxisGlobalOddRoot00SpatialStep09_certificate

/-- The complete genuine tensor transport for original source primitive 10. -/
theorem generatedAxisGlobalOddRoot00FastTensorStep10 :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 6)
        (generatedAxisGlobalTensorIntegerPacket
          (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin09
      generatedAxisGlobalOddRoot00Spatial09) 8) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin10
      generatedAxisGlobalOddRoot00Spatial10) 8 := by
  exact generatedAxisGlobalOddFactorPrimitive_transport 6 _ _ _ _
    2 4 2 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00SpinStep10Envelope_certificate
      generatedAxisGlobalOddRoot00SpatialStep10_certificate

/-- Every physical tensor coordinate is the stated complete packet for the actual source word. -/
theorem generatedAxisGlobalOddRoot00FastTensorState_actual :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis)).2.2 =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin12
      generatedAxisGlobalOddRoot00Spatial12) 4 := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, localConwayRawRepresentation_tensor]
  have hw : generatedAxisGlobalOddSourceRootFiber 0 =
      (([1,6,6,0,5,9,7,7,7,9,0] : List (Fin 10)).map
        generatedAxisGlobalOddSourceFiberLetter).prod := rfl
  rw [hw]
  rw [generatedAxisGlobalOddTensorInteger_packet, ← generatedAxisGlobalOddRoot00InitialFactor]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    map_mul, LinearEquiv.mul_apply]
  rw [generatedAxisGlobalOddRoot00FastTensorStep01,
    generatedAxisGlobalOddRoot00FastTensorStep02,
    generatedAxisGlobalOddRoot00FastTensorStep03,
    generatedAxisGlobalOddRoot00FastTensorStep04,
    generatedAxisGlobalOddRoot00FastTensorStep05,
    generatedAxisGlobalOddRoot00FastTensorStep06,
    generatedAxisGlobalOddRoot00FastTensorStep07,
    generatedAxisGlobalOddRoot00FastTensorStep08,
    generatedAxisGlobalOddRoot00FastTensorStep09,
    generatedAxisGlobalOddRoot00FastTensorStep10,
    generatedAxisGlobalOddRoot00XiInverseFinalTensor_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
