/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseCharacters

/-! Three independent binary characters permit a sign change while preserving
two existing signs. This is the phase prerequisite for the later feasible classes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A third binary character remains nontrivial on the simultaneous kernel
of two independent characters when it is outside their binary span. -/
theorem generatedFeasible_three_characters_kernel {A : Type*} [Group A]
    (χ ψ ρ : A →* Multiplicative (ZMod 2))
    (hχ : Function.Surjective χ) (hψ : Function.Surjective ψ)
    (hρ : Function.Surjective ρ) (hne : ψ ≠ χ)
    (hρχ : ρ ≠ χ) (hρψ : ρ ≠ ψ) (hρprod : ρ ≠ χ * ψ) :
    ∃ a : A, χ a = 1 ∧ ψ a = 1 ∧ ρ a = ofAdd 1 := by
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  obtain ⟨u, hψu, hχu⟩ := generatedAxis_binary_characters_kernel ψ χ hψ hχ hne.symm
  obtain ⟨v, hχv, hψv⟩ := generatedAxis_binary_characters_kernel χ ψ hχ hψ hne
  by_contra! hn
  have hk (a : A) (ha : toAdd (χ a) = 0) (hb : toAdd (ψ a) = 0) :
      toAdd (ρ a) = 0 := by
    rcases hbit (toAdd (ρ a)) with hz | ho
    · exact hz
    · exact False.elim (hn a (toAdd.injective ha) (toAdd.injective hb)
        (toAdd.injective ho))
  have hformula (a : A) : toAdd (ρ a) =
      toAdd (χ a) * toAdd (ρ u) + toAdd (ψ a) * toAdd (ρ v) := by
    rcases hbit (toAdd (χ a)) with hx | hx <;>
      rcases hbit (toAdd (ψ a)) with hy | hy
    · simpa only [hx, hy, zero_mul, zero_add] using hk a hx hy
    · have hc : toAdd (χ (a * v)) = 0 := by
        rw [map_mul, hχv, mul_one]
        exact hx
      have hd : toAdd (ψ (a * v)) = 0 := by
        rw [map_mul, hψv]
        change toAdd (ψ a) + 1 = 0
        rw [hy]
        decide
      have hz := hk (a * v) hc hd
      rw [map_mul] at hz
      change toAdd (ρ a) + toAdd (ρ v) = 0 at hz
      simpa only [hx, hy, zero_mul, one_mul, zero_add] using
        (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq (toAdd (ρ v)))
    · have hc : toAdd (χ (a * u)) = 0 := by
        rw [map_mul, hχu]
        change toAdd (χ a) + 1 = 0
        rw [hx]
        decide
      have hd : toAdd (ψ (a * u)) = 0 := by
        rw [map_mul, hψu, mul_one]
        exact hy
      have hz := hk (a * u) hc hd
      rw [map_mul] at hz
      change toAdd (ρ a) + toAdd (ρ u) = 0 at hz
      simpa only [hx, hy, zero_mul, one_mul, add_zero] using
        (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq (toAdd (ρ u)))
    · have hc : toAdd (χ (a * u * v)) = 0 := by
        rw [χ.map_mul, χ.map_mul, hχu, hχv, mul_one]
        change toAdd (χ a) + 1 = 0
        rw [hx]
        decide
      have hd : toAdd (ψ (a * u * v)) = 0 := by
        rw [ψ.map_mul, ψ.map_mul, hψu, hψv, mul_one]
        change toAdd (ψ a) + 1 = 0
        rw [hy]
        decide
      have hz := hk (a * u * v) hc hd
      rw [ρ.map_mul, ρ.map_mul] at hz
      change toAdd (ρ a) + toAdd (ρ u) + toAdd (ρ v) = 0 at hz
      rw [add_assoc] at hz
      simpa only [hx, hy, one_mul] using
        (eq_neg_of_add_eq_zero_left hz).trans
          (CharTwo.neg_eq (toAdd (ρ u) + toAdd (ρ v)))
  rcases hbit (toAdd (ρ u)) with hu | hu <;> rcases hbit (toAdd (ρ v)) with hv | hv
  · obtain ⟨a, ha⟩ := hρ (ofAdd 1)
    have hz := hformula a
    simp only [ha, hu, hv, mul_zero, add_zero, toAdd_ofAdd] at hz
    exact (by decide : (1 : ZMod 2) ≠ 0) hz
  · apply hρψ
    apply MonoidHom.ext
    intro a
    apply toAdd.injective
    simpa only [hu, hv, mul_zero, mul_one, zero_add] using hformula a
  · apply hρχ
    apply MonoidHom.ext
    intro a
    apply toAdd.injective
    simpa only [hu, hv, mul_zero, mul_one, add_zero] using hformula a
  · apply hρprod
    apply MonoidHom.ext
    intro a
    apply toAdd.injective
    change toAdd (ρ a) = toAdd (χ a) + toAdd (ψ a)
    simpa only [hu, hv, mul_one] using hformula a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
