/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact Pauli fixation of signed affine-subspace states in the actual real spin representation. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.Tactic
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The real spin state supported on a+S, with character b on its translated labels. -/
noncomputable def generatedAxisFourthQAffineSpinState (S : Submodule (ZMod 2) SpinIndex)
    (a b : SpinIndex) : SpinSpace := by
  classical
  exact fun t => if t + a ∈ S then qSign (spinDot b (t + a)) else 0

/-- The literal central correction for a Pauli operator acting on this affine state. -/
def generatedAxisFourthQAffineSpinPhase (q : Q) (a b : SpinIndex) : ZMod 2 :=
  Multiplicative.toAdd q.coeff + spinDot (spinModulation q) a +
    spinDot b (spinTranslation q)

private theorem affine_spin_sign_ne_zero (c : ZMod 2) : qSign c ≠ 0 := by
  intro hc
  have h := qSign_sq c
  rw [hc, zero_mul] at h
  norm_num at h

/-- Every affine state has coefficient one at its chosen base point. -/
theorem generatedAxisFourthQAffineSpinState_base (S : Submodule (ZMod 2) SpinIndex)
    (a b : SpinIndex) : generatedAxisFourthQAffineSpinState S a b a = 1 := by
  simp [generatedAxisFourthQAffineSpinState, ZModModule.add_self]

/-- The affine state is a genuine nonzero vector. -/
theorem generatedAxisFourthQAffineSpinState_ne_zero (S : Submodule (ZMod 2) SpinIndex)
    (a b : SpinIndex) : generatedAxisFourthQAffineSpinState S a b ≠ 0 := by
  intro h
  have he := congrFun h a
  rw [generatedAxisFourthQAffineSpinState_base] at he
  norm_num at he

/-- Once its translation belongs to S, a Pauli operator multiplies the state by its
base-point phase and the modulation character on the translated support. -/
theorem generatedAxisFourthQAffineSpin_apply (S : Submodule (ZMod 2) SpinIndex)
    (a b : SpinIndex) (q : Q) (hv : spinTranslation q ∈ S) (t : SpinIndex) :
    spinOperator q (generatedAxisFourthQAffineSpinState S a b) t =
      qSign (generatedAxisFourthQAffineSpinPhase q a b) *
        qSign (spinDot (spinModulation q) (t + a)) *
          generatedAxisFourthQAffineSpinState S a b t := by
  have hl : t + spinTranslation q + a = (t + a) + spinTranslation q := by
    abel
  have hm : t + spinTranslation q + a ∈ S ↔ t + a ∈ S := by
    rw [hl]
    exact S.add_mem_iff_left hv
  have hb : spinDot b (t + spinTranslation q + a) =
      spinDot b (t + a) + spinDot b (spinTranslation q) := by
    rw [hl, spinDot_add_right]
  have hd : spinDot (spinModulation q) t =
      spinDot (spinModulation q) (t + a) + spinDot (spinModulation q) a := by
    rw [spinDot_add_right, add_assoc, ZModModule.add_self, add_zero]
  change qSign (spinPhase q t) *
      generatedAxisFourthQAffineSpinState S a b (t + spinTranslation q) = _
  by_cases ht : t + a ∈ S
  · simp only [generatedAxisFourthQAffineSpinState, ht, hm.mpr ht, ↓reduceIte]
    rw [hb]
    simp only [spinPhase, generatedAxisFourthQAffineSpinPhase, hd, qSign_add]
    ring
  · have ht' : t + spinTranslation q + a ∉ S := fun h => ht (hm.mp h)
    simp only [generatedAxisFourthQAffineSpinState, ht, ht', ↓reduceIte, mul_zero]

/-- Fixing the actual affine spin state is exactly translation in S, modulation annihilating S,
and vanishing of the literal central phase. -/
theorem generatedAxisFourthQAffineSpin_fixed_iff (S : Submodule (ZMod 2) SpinIndex)
    (a b : SpinIndex) (q : Q) :
    spinOperator q (generatedAxisFourthQAffineSpinState S a b) =
      generatedAxisFourthQAffineSpinState S a b ↔
    spinTranslation q ∈ S ∧
      (∀ s ∈ S, spinDot (spinModulation q) s = 0) ∧
        generatedAxisFourthQAffineSpinPhase q a b = 0 := by
  constructor
  · intro hfix
    have hv : spinTranslation q ∈ S := by
      by_contra hv
      have he := congrFun hfix a
      have hl : a + spinTranslation q + a = spinTranslation q := by
        calc
          _ = spinTranslation q + (a + a) := by abel
          _ = spinTranslation q := by rw [ZModModule.add_self, add_zero]
      change qSign (spinPhase q a) *
          generatedAxisFourthQAffineSpinState S a b (a + spinTranslation q) = _ at he
      rw [generatedAxisFourthQAffineSpinState_base] at he
      simp only [generatedAxisFourthQAffineSpinState, hl, hv, ↓reduceIte, mul_zero] at he
      norm_num at he
    have hp : generatedAxisFourthQAffineSpinPhase q a b = 0 := by
      have he := congrFun hfix a
      rw [generatedAxisFourthQAffineSpin_apply S a b q hv,
        generatedAxisFourthQAffineSpinState_base] at he
      simp only [ZModModule.add_self, spinDot_zero_right, qSign_zero, mul_one] at he
      exact (qSign_eq_one_iff _).mp he
    refine ⟨hv, ?_, hp⟩
    intro s hs
    have hl : (a + s) + a = s := by
      calc
        _ = s + (a + a) := by abel
        _ = s := by rw [ZModModule.add_self, add_zero]
    have he := congrFun hfix (a + s)
    rw [generatedAxisFourthQAffineSpin_apply S a b q hv, hp, qSign_zero, one_mul,
      hl] at he
    have hn : generatedAxisFourthQAffineSpinState S a b (a + s) ≠ 0 := by
      simpa only [generatedAxisFourthQAffineSpinState, hl, hs, ↓reduceIte] using
        affine_spin_sign_ne_zero (spinDot b s)
    exact (qSign_eq_one_iff _).mp ((mul_eq_right₀ hn).mp he)
  · rintro ⟨hv, hm, hp⟩
    funext t
    rw [generatedAxisFourthQAffineSpin_apply S a b q hv, hp, qSign_zero, one_mul]
    by_cases ht : t + a ∈ S
    · rw [hm _ ht, qSign_zero, one_mul]
    · simp only [generatedAxisFourthQAffineSpinState, ht, ↓reduceIte, mul_zero]

/-- The same exact criterion for the bundled actual real Schrödinger representation. -/
theorem generatedAxisFourthQAffineSpin_representation_fixed_iff
    (S : Submodule (ZMod 2) SpinIndex) (a b : SpinIndex) (q : Q) :
    spinRepresentation q (generatedAxisFourthQAffineSpinState S a b) =
      generatedAxisFourthQAffineSpinState S a b ↔
    spinTranslation q ∈ S ∧
      (∀ s ∈ S, spinDot (spinModulation q) s = 0) ∧
        Multiplicative.toAdd q.coeff + spinDot (spinModulation q) a +
          spinDot b (spinTranslation q) = 0 :=
  generatedAxisFourthQAffineSpin_fixed_iff S a b q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
