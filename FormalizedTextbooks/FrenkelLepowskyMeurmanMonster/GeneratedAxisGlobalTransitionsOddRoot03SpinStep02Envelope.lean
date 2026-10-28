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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03SpinStateData

/-! Exact finite envelopes retain every actual nonzero source contribution and prove all omitted coefficients vanish. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Complete finite envelope of the original source primitive. -/
def generatedAxisGlobalOddRoot03SpinStep02Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![
    0x4001,
    0x1004,
    0x1004,
    0x4001,
    0x2008000000000000000000000000000000000000000000000000000000000000,
    0x8002000000000000000000000000000000000000000000000000000000000000,
    0x8002000000000000000000000000000000000000000000000000000000000000,
    0x2008000000000000000000000000000000000000000000000000000000000000,
    0x4001,
    0x1004,
    0x1004,
    0x4001,
    0x2008000000000000000000000000000000000000000000000000000000000000,
    0x8002000000000000000000000000000000000000000000000000000000000000,
    0x8002000000000000000000000000000000000000000000000000000000000000,
    0x2008000000000000000000000000000000000000000000000000000000000000]

/-- Every original physical spin coefficient has its genuine source normalization. -/
theorem generatedAxisGlobalOddRoot03SpinStep02Envelope_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 6 generatedAxisGlobalOddRoot03Spin01 k =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot03Spin02 k := by
  let E := generatedAxisGlobalOddRoot03SpinStep02Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot03Spin01 m ≠ 0 → E ((generatedAxisGlobalOddMonomialLabelEquiv [(0, false)]).symm m) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, false)] generatedAxisGlobalOddRoot03Spin01 k =
        1 * (1 : ℤ) * generatedAxisGlobalOddRoot03Spin02 k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot03Spin02 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (1 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, false)] generatedAxisGlobalOddRoot03Spin01 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 (1 * 1) hi
    (generatedAxisGlobalOddMonomialSpin_zero_outside [(0, false)] _ E hc) hv k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
