/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddMonomialEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSignEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02SpinStateData

/-! Exact finite envelopes retain every actual nonzero source contribution and prove all omitted coefficients vanish. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete finite envelope of the original source primitive. -/
def generatedAxisGlobalOddRoot02SpinStep04Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![
    0xffff,
    0x0,
    0x0,
    0x0,
    0xffff,
    0x0,
    0x0,
    0x0,
    0xffff,
    0x0,
    0x0,
    0x0,
    0xffff,
    0x0,
    0x0,
    0x0]

/-- Every original physical spin coefficient has its genuine source normalization. -/
theorem generatedAxisGlobalOddRoot02SpinStep04Envelope_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot02Spin03 k =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spin04 k := by
  let E := generatedAxisGlobalOddRoot02SpinStep04Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot02Spin03 m ≠ 0 → ∀ a : Fin 64, E (generatedSixthSpinLabelXor m (generatedSixthGrayCodeLabel a)) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot02Spin03 k =
        8 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spin04 k := by
    rw [generatedAxisGlobalOddXiSpinInteger_eq_cached]
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot02Spin04 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot02Spin03 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (8 * 1) hi
    (generatedAxisGlobalOddXiSpin_zero_outside _ E hc) hv k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
