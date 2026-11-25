/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean`
and
`P2M/Sol/S_ModularCurve_surjective_specialLinearGroup_map_zmod.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.LinearCombination

/-!
# Surjectivity of reduction from `SL(2, ℤ)` to `SL(2, ZMod N)`

This file proves that reduction `SL(2, ℤ) → SL(2, ZMod N)` is surjective.

## Main statement

* `Matrix.SpecialLinearGroup.map_intCastRingHom_zmod_surjective`
-/
namespace FrickeFunctions.SLTwoZModSurjective

open Matrix Finset

namespace ModularCurve

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [ite_eq_right (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [ite_eq_left hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [ite_eq_right hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [ite_eq_right h] at hpγ
  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  · by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      have h3' : p ∣ primeSel γ d₀ * N := by
        have heq : (primeSel γ d₀ : ℤ) * (N : ℤ) = ((primeSel γ d₀ * N : ℕ) : ℤ) := by
          push_cast; ring
        rw [heq] at h3
        exact natCast_dvd_int.mp h3
      rcases (Nat.Prime.dvd_mul pp).mp h3' with h4 | h4
      · exact not_dvd_primeSel pp hpd h4
      · exact Hγ p pp h1 hpd (natCast_dvd_int.mpr h4)
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  · push_cast
    simp

private theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by
  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d
  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h
  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))
  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ
  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez
  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this
  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  · push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  · push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

end ModularCurve

open scoped MatrixGroups

/-- Reduction modulo `N`, `SL(2, ℤ) → SL(2, ZMod N)`, is surjective. -/
public theorem _root_.Matrix.SpecialLinearGroup.map_intCastRingHom_zmod_surjective (N : ℕ) [NeZero
    N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := ModularCurve.exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end SLTwoZModSurjective

end FrickeFunctions
