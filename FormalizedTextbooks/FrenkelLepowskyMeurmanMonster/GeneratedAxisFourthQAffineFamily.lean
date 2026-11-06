/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual common affine-state stabilizer and its exact binary coordinate constraints. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

variable {J : Type*}

/-- The binary translation-modulation pairs satisfying all common affine-state constraints. -/
def generatedAxisFourthQAffineFamilyKernel (S : Submodule (ZMod 2) SpinIndex)
    (a b : J → SpinIndex) (j₀ : J) : Submodule (ZMod 2) (SpinIndex × SpinIndex) where
  carrier := {p | p.1 ∈ S ∧ (∀ s ∈ S, spinDot p.2 s = 0) ∧
    ∀ j, spinDot p.2 (a j + a j₀) + spinDot (b j + b j₀) p.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hxu, hxm, hx⟩ ⟨hyu, hym, hy⟩
    refine ⟨S.add_mem hxu hyu, ?_, ?_⟩
    · intro s hs
      exact (spinDot_add_left _ _ _).trans (by rw [hxm s hs, hym s hs, add_zero])
    · intro j
      change spinDot (x.2 + y.2) (a j + a j₀) +
        spinDot (b j + b j₀) (x.1 + y.1) = 0
      simp only [spinDot_add_left, spinDot_add_right] at hx hy ⊢
      linear_combination hx j + hy j
  smul_mem' := by
    intro c x hx
    fin_cases c
    · change (0 : ZMod 2) • x ∈ _
      simp
    · change (1 : ZMod 2) • x ∈ _
      simpa only [one_smul] using hx

/-- Membership in the binary kernel is exactly the stated translation-modulation constraints. -/
theorem generatedAxisFourthQAffineFamilyKernel_mem (S : Submodule (ZMod 2) SpinIndex)
    (a b : J → SpinIndex) (j₀ : J) (u m : SpinIndex) :
    (u, m) ∈ generatedAxisFourthQAffineFamilyKernel S a b j₀ ↔
      u ∈ S ∧ (∀ s ∈ S, spinDot m s = 0) ∧
        ∀ j, spinDot m (a j + a j₀) + spinDot (b j + b j₀) u = 0 := Iff.rfl

/-- The actual subgroup of Q fixing every specified real affine spin state. -/
def generatedAxisFourthQAffineFamilyStabilizer (S : Submodule (ZMod 2) SpinIndex)
    (a b : J → SpinIndex) : Subgroup Q where
  carrier := {q | ∀ j, spinRepresentation q (generatedAxisFourthQAffineSpinState S (a j) (b j)) =
    generatedAxisFourthQAffineSpinState S (a j) (b j)}
  one_mem' := by intro j; simp
  mul_mem' := by
    intro q r hq hr j
    rw [map_mul, LinearEquiv.mul_apply, hr j, hq j]
  inv_mem' := by
    intro q hq j
    have h := congrArg (spinRepresentation q⁻¹) (hq j)
    simpa only [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      LinearEquiv.coe_one, id_eq] using h.symm

/-- Common actual fixation is equivalent to the binary kernel and its uniquely prescribed
literal central coefficient. -/
theorem generatedAxisFourthQAffineFamily_mem_iff (S : Submodule (ZMod 2) SpinIndex)
    (a b : J → SpinIndex) (j₀ : J) (q : Q) :
    q ∈ generatedAxisFourthQAffineFamilyStabilizer S a b ↔
      (spinTranslation q, spinModulation q) ∈ generatedAxisFourthQAffineFamilyKernel S a b j₀ ∧
        Multiplicative.toAdd q.coeff = spinDot (spinModulation q) (a j₀) +
          spinDot (b j₀) (spinTranslation q) := by
  constructor
  · intro hq
    have href := (generatedAxisFourthQAffineSpin_representation_fixed_iff S (a j₀) (b j₀) q).mp
      (hq j₀)
    refine ⟨⟨href.1, href.2.1, ?_⟩, ?_⟩
    · intro j
      have hj := (generatedAxisFourthQAffineSpin_representation_fixed_iff S (a j) (b j) q).mp
        (hq j)
      rw [spinDot_add_right, spinDot_add_left]
      have hc := ZModModule.add_self (Multiplicative.toAdd q.coeff)
      linear_combination hj.2.2 + href.2.2 - hc
    · have ha := ZModModule.add_self (spinDot (spinModulation q) (a j₀))
      have hb := ZModModule.add_self (spinDot (b j₀) (spinTranslation q))
      linear_combination href.2.2 - ha - hb
  · rintro ⟨⟨hu, hm, hj⟩, hc⟩ j
    apply (generatedAxisFourthQAffineSpin_representation_fixed_iff S (a j) (b j) q).mpr
    refine ⟨hu, hm, ?_⟩
    have hd := hj j
    rw [spinDot_add_right, spinDot_add_left] at hd
    linear_combination hd + hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
