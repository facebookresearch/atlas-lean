/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSpinSupport

/-! Actual whole-state fixation determines the modulation character on signed support periods. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine signed translation period determines the fixing Pauli phase on every nonzero entry. -/
theorem generatedSpinSupport_fixed_phase (q : Q) (f : SpinSpace) (c : ZMod 2)
    (hf : spinRepresentation q f = f)
    (hp : ∀ t, f (t + spinTranslation q) = qSign c * f t)
    (t : SpinIndex) (ht : f t ≠ 0) : spinPhase q t + c = 0 := by
  have he := (generatedSpinSupport_fixed_iff q f).mp hf t
  rw [hp t, ← mul_assoc, ← qSign_add] at he
  have hs : qSign (spinPhase q t + c) = 1 := by
    apply (mul_left_inj' ht).mp
    simpa only [one_mul] using he
  exact (qSign_eq_one_iff _).mp hs

/-- A fixing modulation is constant on the actual support of a signed translation eigenstate. -/
theorem generatedSpinSupport_fixed_modulation_equal (q : Q) (f : SpinSpace) (c : ZMod 2)
    (hf : spinRepresentation q f = f)
    (hp : ∀ t, f (t + spinTranslation q) = qSign c * f t)
    (t u : SpinIndex) (ht : f t ≠ 0) (hu : f u ≠ 0) :
    spinDot (spinModulation q) t = spinDot (spinModulation q) u := by
  have htphase := generatedSpinSupport_fixed_phase q f c hf hp t ht
  have huphase := generatedSpinSupport_fixed_phase q f c hf hp u hu
  have he : spinPhase q t = spinPhase q u :=
    add_right_cancel (htphase.trans huphase.symm)
  exact add_left_cancel he

/-- The fixing modulation annihilates every actual difference of nonzero support labels. -/
theorem generatedSpinSupport_fixed_modulation_difference (q : Q) (f : SpinSpace) (c : ZMod 2)
    (hf : spinRepresentation q f = f)
    (hp : ∀ t, f (t + spinTranslation q) = qSign c * f t)
    (t u : SpinIndex) (ht : f t ≠ 0) (hu : f u ≠ 0) :
    spinDot (spinModulation q) (t + u) = 0 := by
  rw [spinDot_add_right, generatedSpinSupport_fixed_modulation_equal q f c hf hp t u ht hu]
  exact ZModModule.add_self _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
