/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStateData

/-! Complete original forward return and actual inverse cancellation at source stage 1. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete possible support of the genuine original forward source return. -/
def generatedAxisGlobalOddRoot03XiInverse01Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![0xffff, 0x0, 0x0, 0x0, 0xffff, 0x0, 0x0, 0x0, 0xffff, 0x0, 0x0, 0x0, 0xffff, 0x0, 0x0, 0x0]

/-- Every original physical spin coordinate has its exact source normalization. -/
theorem generatedAxisGlobalOddRoot03XiInverse01Spin_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot03Spin01 k =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot03Spin00 k := by
  let E := generatedAxisGlobalOddRoot03XiInverse01Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot03Spin01 m ≠ 0 → ∀ a : Fin 64,
      E (generatedSixthSpinLabelXor m (generatedSixthGrayCodeLabel a)) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot03Spin01 k =
        8 * (1 : ℤ) * generatedAxisGlobalOddRoot03Spin00 k := by
    rw [generatedAxisGlobalOddXiSpinInteger_eq_cached]
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot03Spin00 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot03Spin01 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (8 * 1) hi
    (generatedAxisGlobalOddXiSpin_zero_outside _ E hc) hv k

/-- Every original physical spatial coordinate has its exact source normalization. -/
theorem generatedAxisGlobalOddRoot03XiInverse01Spatial_certificate (i : Fin 24) :
    (1 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot03Spatial01 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot03Spatial00 i := by
  revert i
  decide +kernel

/-- Genuine inverse cancellation gives the complete actual original source tensor step. -/
theorem generatedAxisGlobalOddRoot03XiInverse01Tensor_actual :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin00 generatedAxisGlobalOddRoot03Spatial00) 1) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot03Spin01 generatedAxisGlobalOddRoot03Spatial01) 2 := by
  have hforward := generatedAxisGlobalOddFactorPrimitive_transport 0
    generatedAxisGlobalOddRoot03Spin01 generatedAxisGlobalOddRoot03Spin00 generatedAxisGlobalOddRoot03Spatial01 generatedAxisGlobalOddRoot03Spatial00
    1 2 1 1 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot03XiInverse01Spin_certificate generatedAxisGlobalOddRoot03XiInverse01Spatial_certificate
  have hinv : generatedAxisGlobalOddSourceFiberLetter 1 =
      (generatedAxisGlobalOddSourceFiberLetter 0)⁻¹ := rfl
  rw [hinv, map_inv, ← hforward]
  exact LinearEquiv.symm_apply_apply _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
