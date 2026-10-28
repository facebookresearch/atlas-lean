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
def generatedAxisGlobalOddRoot00SpinStep10Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![
    0x6969000000000000000000009696000000006969000000000000000000009696,
    0x969600000000000000000000696996960000000000000000000069690000,
    0x696900000000000000000000969669690000000000000000000096960000,
    0x9696000000000000000000006969000000009696000000000000000000006969,
    0x9696000069690000000000000000969600006969000000000000,
    0x69690000969600000000000000000000000069690000969600000000,
    0x96960000696900000000000000000000000096960000696900000000,
    0x6969000096960000000000000000696900009696000000000000,
    0x6969000000000000000000009696000000006969000000000000000000009696,
    0x969600000000000000000000696996960000000000000000000069690000,
    0x696900000000000000000000969669690000000000000000000096960000,
    0x9696000000000000000000006969000000009696000000000000000000006969,
    0x9696000069690000000000000000969600006969000000000000,
    0x69690000969600000000000000000000000069690000969600000000,
    0x96960000696900000000000000000000000096960000696900000000,
    0x6969000096960000000000000000696900009696000000000000]

/-- Every original physical spin coefficient has its genuine source normalization. -/
theorem generatedAxisGlobalOddRoot00SpinStep10Envelope_certificate (k : Fin 4096) :
    (2 : ℤ) * generatedAxisGlobalOddSpinPrimitive 6 generatedAxisGlobalOddRoot00Spin09 k =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spin10 k := by
  let E := generatedAxisGlobalOddRoot00SpinStep10Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot00Spin09 m ≠ 0 → E ((generatedAxisGlobalOddMonomialLabelEquiv [(0, false)]).symm m) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (2 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, false)] generatedAxisGlobalOddRoot00Spin09 k =
        1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spin10 k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot00Spin10 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (2 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, false)] generatedAxisGlobalOddRoot00Spin09 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 2 (1 * 2) hi
    (generatedAxisGlobalOddMonomialSpin_zero_outside [(0, false)] _ E hc) hv k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
