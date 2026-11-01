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
def generatedAxisGlobalOddRoot00SpinStep09Envelope : Fin 4096 → Bool :=
  generatedAxisGlobalOddSpinEnvelope ![
    0x4001800280024001200810041004200880024001400180021004200820081004,
    0x1004200820081004800240014001800220081004100420084001800280024001,
    0x1004200820081004800240014001800220081004100420084001800280024001,
    0x4001800280024001200810041004200880024001400180021004200820081004,
    0x8002400140018002100420082008100440018002800240012008100410042008,
    0x2008100410042008400180028002400110042008200810048002400140018002,
    0x2008100410042008400180028002400110042008200810048002400140018002,
    0x8002400140018002100420082008100440018002800240012008100410042008,
    0x4001800280024001200810041004200880024001400180021004200820081004,
    0x1004200820081004800240014001800220081004100420084001800280024001,
    0x1004200820081004800240014001800220081004100420084001800280024001,
    0x4001800280024001200810041004200880024001400180021004200820081004,
    0x8002400140018002100420082008100440018002800240012008100410042008,
    0x2008100410042008400180028002400110042008200810048002400140018002,
    0x2008100410042008400180028002400110042008200810048002400140018002,
    0x8002400140018002100420082008100440018002800240012008100410042008]

/-- Every original physical spin coefficient has its genuine source normalization. -/
theorem generatedAxisGlobalOddRoot00SpinStep09Envelope_certificate (k : Fin 4096) :
    (2 : ℤ) * generatedAxisGlobalOddSpinPrimitive 6 generatedAxisGlobalOddRoot00Spin08 k =
      1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spin09 k := by
  let E := generatedAxisGlobalOddRoot00SpinStep09Envelope
  have hc : ∀ m : Fin 4096, generatedAxisGlobalOddRoot00Spin08 m ≠ 0 → E ((generatedAxisGlobalOddMonomialLabelEquiv [(0, false)]).symm m) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (2 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, false)] generatedAxisGlobalOddRoot00Spin08 k =
        1 * (2 : ℤ) * generatedAxisGlobalOddRoot00Spin09 k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddRoot00Spin09 k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  change (2 : ℤ) * generatedAxisGlobalOddMonomialSpinInteger [(0, false)] generatedAxisGlobalOddRoot00Spin08 k = _
  exact generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 2 (1 * 2) hi
    (generatedAxisGlobalOddMonomialSpin_zero_outside [(0, false)] _ E hc) hv k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
