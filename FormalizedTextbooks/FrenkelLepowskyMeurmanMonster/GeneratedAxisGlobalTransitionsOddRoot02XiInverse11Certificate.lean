/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStateData

/-! Complete original forward return and actual inverse cancellation at source stage 11. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete possible support of the genuine original forward source return. -/
def generatedAxisGlobalOddRoot02XiInverse11Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff]

/-- Every original physical spin coordinate has its exact source normalization. -/
theorem generatedAxisGlobalOddRoot02XiInverse11Spin_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot02Spin11 k =
      8 * (2 : ℤ) * generatedAxisGlobalOddRoot02Spin10 k := by
  let E := generatedAxisGlobalOddRoot02XiInverse11Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot02Spin11 m ≠ 0 → ∀ a : Fin 64,
      E (generatedSixthSpinLabelXor m (generatedSixthGrayCodeLabel a)) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot02Spin11 k =
        8 * (2 : ℤ) * generatedAxisGlobalOddRoot02Spin10 k := by
    rw [generatedAxisGlobalOddXiSpinInteger_eq_cached]
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot02Spin10 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot02Spin11 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (8 * 2) hi
    (generatedAxisGlobalOddXiSpin_zero_outside _ E hc) hv k

/-- Every original physical spatial coordinate has its exact source normalization. -/
theorem generatedAxisGlobalOddRoot02XiInverse11Spatial_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot02Spatial11 i =
      2 * (4 : ℤ) * generatedAxisGlobalOddRoot02Spatial10 i := by
  revert i
  decide +kernel

/-- Genuine inverse cancellation gives the complete actual original source tensor step. -/
theorem generatedAxisGlobalOddRoot02XiInverse11Tensor_actual :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin10 generatedAxisGlobalOddRoot02Spatial10) 4) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot02Spin11 generatedAxisGlobalOddRoot02Spatial11) 8 := by
  have hforward := generatedAxisGlobalOddFactorPrimitive_transport 0
    generatedAxisGlobalOddRoot02Spin11 generatedAxisGlobalOddRoot02Spin10 generatedAxisGlobalOddRoot02Spatial11 generatedAxisGlobalOddRoot02Spatial10
    2 4 1 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot02XiInverse11Spin_certificate generatedAxisGlobalOddRoot02XiInverse11Spatial_certificate
  have hinv : generatedAxisGlobalOddSourceFiberLetter 1 =
      (generatedAxisGlobalOddSourceFiberLetter 0)⁻¹ := rfl
  rw [hinv, map_inv, ← hforward]
  exact LinearEquiv.symm_apply_apply _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
