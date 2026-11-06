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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04SpinStateData

/-! Exact finite envelopes retain every actual nonzero source contribution and prove all omitted coefficients vanish. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete finite envelope of the original source primitive. -/
def generatedAxisGlobalOddRoot04SpinStep06Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![
    0x0,
    0x0,
    0x10001,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
    0x10001,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0]

/-- Every original physical spin coefficient has its genuine source normalization. -/
theorem generatedAxisGlobalOddRoot04SpinStep06Envelope_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 3 generatedAxisGlobalOddRoot04Spin05 k =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spin06 k := by
  let E := generatedAxisGlobalOddRoot04SpinStep06Envelope
  have hc : ∀ e : Fin 2048,
    (generatedAxisGlobalOddRoot04Spin05 (generatedAxisGlobalTensorLowLabel e) ≠ 0 ∨
     generatedAxisGlobalOddRoot04Spin05 (generatedAxisGlobalTensorHighLabel e) ≠ 0 ∨
     generatedAxisGlobalOddRoot04Spin05 (generatedAxisGlobalTensorLowLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 16) e)) ≠ 0 ∨
     generatedAxisGlobalOddRoot04Spin05 (generatedAxisGlobalTensorHighLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 16) e)) ≠ 0) →
     E (generatedAxisGlobalTensorLowLabel e) = true ∧ E (generatedAxisGlobalTensorHighLabel e) = true := by
    apply generatedAxisGlobalOddLowEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddSignSpinInteger 16 generatedAxisGlobalOddRoot04Spin05 k =
        2 * (1 : ℤ) * generatedAxisGlobalOddRoot04Spin06 k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot04Spin06 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddSignSpinInteger 16 generatedAxisGlobalOddRoot04Spin05 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (2 * 1) hi
    (generatedAxisGlobalOddSignSpin_zero_outside 16 _ E hc) hv k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
