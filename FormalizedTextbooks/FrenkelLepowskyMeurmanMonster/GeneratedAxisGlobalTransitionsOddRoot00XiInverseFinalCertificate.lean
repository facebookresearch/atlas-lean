/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData

/-! A complete original forward return certifies the genuine inverse Xi source step without any intermediate surrogate state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete possible support of the actual forward source return. -/
def generatedAxisGlobalOddRoot00XiInverseFinalEnvelope : Fin 4096 → Bool := generatedAxisGlobalOddSpinEnvelope ![
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff,
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff,
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff,
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffffffff0000ffff00000000ffffffff00000000ffff0000ffffffff0000,
    0xffff00000000ffff0000ffffffff00000000ffffffff0000ffff00000000ffff]

/-- Every original forward return coefficient has its exact genuine normalization. -/
theorem generatedAxisGlobalOddRoot00XiInverseFinalSpin_certificate (k : Fin 4096) :
    (2 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot00Spin12 k =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin10 k := by
  let E := generatedAxisGlobalOddRoot00XiInverseFinalEnvelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot00Spin12 m ≠ 0 → ∀ a : Fin 64,
      E (generatedSixthSpinLabelXor m (generatedSixthGrayCodeLabel a)) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (2 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot00Spin12 k =
        8 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin10 k := by
    rw [generatedAxisGlobalOddXiSpinInteger_eq_cached]
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot00Spin10 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (2 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot00Spin12 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 2 (8 * 1) hi
    (generatedAxisGlobalOddXiSpin_zero_outside _ E hc) hv k

/-- Every original forward spatial return has the matching genuine dyadic normalization. -/
theorem generatedAxisGlobalOddRoot00XiInverseFinalSpatial_certificate (i : Fin 24) :
    (4 : ℤ) * generatedAxisGlobalOddSpatialPrimitive 0 generatedAxisGlobalOddRoot00Spatial12 i =
      2 * (4 : ℤ) * generatedAxisGlobalOddRoot00Spatial10 i := by
  revert i
  decide +kernel

/-- Cancelling the genuine forward return proves the entire actual original inverse Xi transport. -/
theorem generatedAxisGlobalOddRoot00XiInverseFinalTensor_actual :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter 1)
      (generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin10 generatedAxisGlobalOddRoot00Spatial10) 8) =
    generatedAxisGlobalTensorIntegerPacket
      (generatedAxisGlobalOddTensorFactor generatedAxisGlobalOddRoot00Spin12 generatedAxisGlobalOddRoot00Spatial12) 4 := by
  have hforward := generatedAxisGlobalOddFactorPrimitive_transport 0
    generatedAxisGlobalOddRoot00Spin12 generatedAxisGlobalOddRoot00Spin10
    generatedAxisGlobalOddRoot00Spatial12 generatedAxisGlobalOddRoot00Spatial10
    1 4 2 4 (by decide) (by decide) (by decide) (by decide)
    generatedAxisGlobalOddRoot00XiInverseFinalSpin_certificate generatedAxisGlobalOddRoot00XiInverseFinalSpatial_certificate
  have hinv : generatedAxisGlobalOddSourceFiberLetter 1 =
      (generatedAxisGlobalOddSourceFiberLetter 0)⁻¹ := rfl
  rw [hinv, map_inv, ← hforward]
  exact LinearEquiv.symm_apply_apply _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
