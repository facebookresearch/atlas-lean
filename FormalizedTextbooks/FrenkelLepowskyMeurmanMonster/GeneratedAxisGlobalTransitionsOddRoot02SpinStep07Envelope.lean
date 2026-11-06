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
def generatedAxisGlobalOddRoot02SpinStep07Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![
    0x0,
    0x50000000000500000000000000000000000000000a00000000a0000000,
    0x0,
    0x0,
    0xa00000000000000000000a00000000000000000500000000000000000000005,
    0x0,
    0x0,
    0x0,
    0x0,
    0x50000000000500000000000000000000000000000a00000000a0000000,
    0x0,
    0x0,
    0xa00000000000000000000a00000000000000000500000000000000000000005,
    0x0,
    0x0,
    0x0]

/-- Every original physical spin coefficient has its genuine source normalization. -/
theorem generatedAxisGlobalOddRoot02SpinStep07Envelope_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 7 generatedAxisGlobalOddRoot02Spin06 k =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spin07 k := by
  let E := generatedAxisGlobalOddRoot02SpinStep07Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot02Spin06 m ≠ 0 → E ((generatedAxisGlobalOddMonomialLabelEquiv [(0, true)]).symm m) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, true)] generatedAxisGlobalOddRoot02Spin06 k =
        1 * (1 : ℤ) * generatedAxisGlobalOddRoot02Spin07 k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot02Spin07 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, true)] generatedAxisGlobalOddRoot02Spin06 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (1 * 1) hi
    (generatedAxisGlobalOddMonomialSpin_zero_outside [(0, true)] _ E hc) hv k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
