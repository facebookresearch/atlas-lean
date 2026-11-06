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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData

/-! Exact finite envelopes retain every actual nonzero source contribution and prove all omitted coefficients vanish. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete finite envelope of the original source primitive. -/
def generatedAxisGlobalOddRoot00SpinStep07Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![
    0x40000100400001000008002000080020,
    0x8002000080020000040000100400001,
    0x0,
    0x0,
    0x8000020080000200000400100004001000000000000000000000000000000000,
    0x400100004001000008000020080000200000000000000000000000000000000,
    0x0,
    0x0,
    0x40000100400001000008002000080020,
    0x8002000080020000040000100400001,
    0x0,
    0x0,
    0x8000020080000200000400100004001000000000000000000000000000000000,
    0x400100004001000008000020080000200000000000000000000000000000000,
    0x0,
    0x0]

/-- Every original physical spin coefficient has its genuine source normalization. -/
theorem generatedAxisGlobalOddRoot00SpinStep07Envelope_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 5 generatedAxisGlobalOddRoot00Spin06 k =
      2 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin07 k := by
  let E := generatedAxisGlobalOddRoot00SpinStep07Envelope
  have hc : ∀ e : Fin 2048,
    (generatedAxisGlobalOddRoot00Spin06 (generatedAxisGlobalTensorLowLabel e) ≠ 0 ∨
     generatedAxisGlobalOddRoot00Spin06 (generatedAxisGlobalTensorHighLabel e) ≠ 0 ∨
     generatedAxisGlobalOddRoot00Spin06 (generatedAxisGlobalTensorLowLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 32) e)) ≠ 0 ∨
     generatedAxisGlobalOddRoot00Spin06 (generatedAxisGlobalTensorHighLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 32) e)) ≠ 0) →
     E (generatedAxisGlobalTensorLowLabel e) = true ∧ E (generatedAxisGlobalTensorHighLabel e) = true := by
    apply generatedAxisGlobalOddLowEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddSignSpinInteger 32 generatedAxisGlobalOddRoot00Spin06 k =
        2 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin07 k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot00Spin07 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddSignSpinInteger 32 generatedAxisGlobalOddRoot00Spin06 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (2 * 1) hi
    (generatedAxisGlobalOddSignSpin_zero_outside 32 _ E hc) hv k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
