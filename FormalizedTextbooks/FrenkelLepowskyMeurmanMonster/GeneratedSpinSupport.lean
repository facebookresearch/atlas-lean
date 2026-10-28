/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

/-! Genuine Pauli fixation forces translation periods of the actual spin-state support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual nonzero coordinates of a spin state. -/
def generatedSpinSupport (f : SpinSpace) : Set SpinIndex := {t | f t ≠ 0}

/-- Every genuine binary Pauli phase is nonzero. -/
theorem generatedSpinSupport_phase_ne_zero (c : ZMod 2) : qSign c ≠ 0 := by
  intro h
  have hs := qSign_sq c
  rw [h, zero_mul] at hs
  norm_num at hs

/-- Original spin action has translated support, with every central phase retained. -/
theorem generatedSpinSupport_action (q : Q) (f : SpinSpace) (t : SpinIndex) :
    t ∈ generatedSpinSupport (spinRepresentation q f) ↔
      t + spinTranslation q ∈ generatedSpinSupport f := by
  change qSign (spinPhase q t) * f (t + spinTranslation q) ≠ 0 ↔
    f (t + spinTranslation q) ≠ 0
  rw [mul_ne_zero_iff]
  exact and_iff_right (generatedSpinSupport_phase_ne_zero (spinPhase q t))

/-- Fixing the whole actual spin state forces its support to have the genuine translation period. -/
theorem generatedSpinSupport_fixed_translation (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q f = f) (t : SpinIndex) :
    f (t + spinTranslation q) ≠ 0 ↔ f t ≠ 0 := by
  have h := generatedSpinSupport_action q f t
  rw [hf] at h
  exact h.symm

/-- Whole-state fixation is exactly the original signed coefficient equation at every label. -/
theorem generatedSpinSupport_fixed_iff (q : Q) (f : SpinSpace) :
    spinRepresentation q f = f ↔
      ∀ t, qSign (spinPhase q t) * f (t + spinTranslation q) = f t := by
  change (fun t => qSign (spinPhase q t) * f (t + spinTranslation q)) = f ↔ _
  exact funext_iff

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
