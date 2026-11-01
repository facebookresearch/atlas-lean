/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStateData

/-! A complete original forward return certifies the genuine inverse Xi source step without any intermediate surrogate state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete possible support of the actual forward source return. -/
def generatedAxisGlobalOddRoot06XiInverse08Envelope : Fin 4096 → Bool := generatedAxisGlobalOddSpinEnvelope ![
    0xffffffff0000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0xffffffff0000,
    0xffffffff0000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0xffffffff0000,
    0xffffffff0000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0xffffffff0000,
    0xffffffff0000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0xffffffff0000]

/-- Every original forward return coefficient has its exact genuine normalization. -/
theorem generatedAxisGlobalOddRoot06XiInverse08Spin_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot06Spin08 k =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot06Spin06 k := by
  let E := generatedAxisGlobalOddRoot06XiInverse08Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot06Spin08 m ≠ 0 → ∀ a : Fin 64,
      E (generatedSixthSpinLabelXor m (generatedSixthGrayCodeLabel a)) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot06Spin08 k =
        8 * (1 : ℤ) * generatedAxisGlobalOddRoot06Spin06 k := by
    rw [generatedAxisGlobalOddXiSpinInteger_eq_cached]
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot06Spin06 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot06Spin08 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (8 * 1) hi
    (generatedAxisGlobalOddXiSpin_zero_outside _ E hc) hv k

/-- Every original forward spatial return has the matching genuine dyadic normalization. -/
theorem generatedAxisGlobalOddRoot06XiInverse08Spatial_certificate (i : Fin 24) :
    (2 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot06Spatial08 i =
      2 * (2 : ℤ) * generatedAxisGlobalOddRoot06Spatial06 i := by
  revert i
  decide +kernel

/-- Cancelling the genuine forward return proves the entire actual original inverse Xi transport. -/
theorem generatedAxisGlobalOddRoot06XiInverse08Tensor_actual :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin06 generatedAxisGlobalOddRoot06Spatial06) 2) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot06Spin08 generatedAxisGlobalOddRoot06Spatial08) 2 := by
  have hforward := generatedAxisGlobalOddFactorPrimitive_transport 0
    generatedAxisGlobalOddRoot06Spin08 generatedAxisGlobalOddRoot06Spin06
    generatedAxisGlobalOddRoot06Spatial08 generatedAxisGlobalOddRoot06Spatial06
    1 2 1 2 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot06XiInverse08Spin_certificate generatedAxisGlobalOddRoot06XiInverse08Spatial_certificate
  have hinv : generatedAxisGlobalOddSourceFiberLetter 1 =
      (generatedAxisGlobalOddSourceFiberLetter 0)⁻¹ := rfl
  rw [hinv, map_inv, ← hforward]
  exact LinearEquiv.symm_apply_apply _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
