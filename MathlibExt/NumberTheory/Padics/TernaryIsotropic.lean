/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Theorems/Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two.lean`
and
`P2M/Sol/S_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two.lean`
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

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Ternary isotropy over `ℚ_[p]` at odd primes
-/
@[expose] public section

namespace P2HasseMinkPadicPort

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

private theorem norm_lt_one_of_toZMod_eq_zero {c : ℤ_[p]} (h : PadicInt.toZMod c = 0) : ‖c‖ < 1
  := by
  have : c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal] at this
  exact PadicInt.mem_nonunits.mp this

private theorem norm_eq_one_of_toZMod_ne_zero {c : ℤ_[p]} (h : PadicInt.toZMod c ≠ 0) : ‖c‖ = 1
  := by
  refine le_antisymm (PadicInt.norm_le_one c) (not_lt.mp fun hlt ↦ h ?_)
  have : c ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact PadicInt.mem_nonunits.mpr hlt
  exact this

private theorem exists_sq_eq_of_toZMod_eq_sq (hp2 : p ≠ 2) {c : ℤ_[p]} {s : ZMod p} (hs : s ≠ 0)
    (hcs : PadicInt.toZMod c = s ^ 2) : ∃ t : ℤ_[p], t ^ 2 = c := by
  obtain ⟨sl, hsl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) s
  have hslnorm : ‖sl‖ = 1 := norm_eq_one_of_toZMod_ne_zero (by rw [hsl]; exact hs)
  have htwo : ‖(2 : ℤ_[p])‖ = 1 := by
    have h := (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
      ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    simpa using h

  set F : ℤ_[p][X] := X ^ 2 - C c with hF
  have hFeval : aeval sl F = sl ^ 2 - c := by simp [hF]
  have hF'eval : aeval sl (derivative F) = 2 * sl := by
    simp [hF]; norm_num
  have hnormF' : ‖aeval sl (derivative F)‖ = 1 := by
    rw [hF'eval, norm_mul, htwo, hslnorm, one_mul]
  have hnormF : ‖aeval sl F‖ < 1 := by
    rw [hFeval]
    apply norm_lt_one_of_toZMod_eq_zero
    rw [map_sub, map_pow, hsl, hcs, sub_self]
  have hhens : ‖aeval sl F‖ < ‖aeval sl (derivative F)‖ ^ 2 := by
    rw [hnormF', one_pow]; exact hnormF
  obtain ⟨t, ht, -⟩ := hensels_lemma hhens
  refine ⟨t, ?_⟩
  have : aeval t F = t ^ 2 - c := by simp [hF]
  rw [this] at ht
  exact sub_eq_zero.mp ht

end P2HasseMinkPadicPort

open P2HasseMinkPadicPort Polynomial in
/-- **Ternary isotropy over `ℚ_[p]` for odd `p`.** If `p` is an odd prime and
`a, b` are p-adic numbers of norm `1`, then `z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0`
has a nontrivial solution in `ℚ_[p]`. -/
public theorem Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  have hpr : p.Prime := Fact.out

  set a₀ : ℤ_[p] := ⟨a, ha.le⟩ with ha₀
  set b₀ : ℤ_[p] := ⟨b, hb.le⟩ with hb₀
  have ha₀n : ‖a₀‖ = 1 := ha
  have hb₀n : ‖b₀‖ = 1 := hb
  have hares : PadicInt.toZMod a₀ ≠ 0 := fun h ↦ by
    have := norm_lt_one_of_toZMod_eq_zero h; rw [ha₀n] at this; exact lt_irrefl _ this
  have hbres : PadicInt.toZMod b₀ ≠ 0 := fun h ↦ by
    have := norm_lt_one_of_toZMod_eq_zero h; rw [hb₀n] at this; exact lt_irrefl _ this

  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact hpr.eq_two_or_odd.resolve_left hp
  have hf : (X ^ 2 - C (PadicInt.toZMod b₀) : (ZMod p)[X]).degree = 2 := by
    rw [degree_X_pow_sub_C (by norm_num)]; rfl
  have hg : (C (-PadicInt.toZMod a₀) * X ^ 2 : (ZMod p)[X]).degree = 2 := by
    rw [degree_C_mul_X_pow 2 (neg_ne_zero.mpr hares)]; rfl
  obtain ⟨z₀, x₀, hzx⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hzx

  by_cases hz₀ : z₀ = 0
  ·
    have hx₀ : x₀ ≠ 0 := by
      intro hx
      apply hbres
      rw [hz₀, hx] at hzx
      linear_combination -hzx
    have ha₀unit : IsUnit a₀ := PadicInt.isUnit_iff.mpr ha₀n
    obtain ⟨u, hu⟩ := ha₀unit

    set c : ℤ_[p] := -b₀ * ↑u⁻¹ with hc
    have haures : PadicInt.toZMod a₀ * PadicInt.toZMod (↑u⁻¹ : ℤ_[p]) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    have hcres : PadicInt.toZMod c = x₀ ^ 2 := by
      rw [hc, map_mul, map_neg]
      have e1 : PadicInt.toZMod b₀ = -(PadicInt.toZMod a₀ * x₀ ^ 2) := by
        rw [hz₀] at hzx; linear_combination -hzx
      rw [e1]
      linear_combination (x₀ ^ 2) * haures
    obtain ⟨w, hw⟩ := exists_sq_eq_of_toZMod_eq_sq hp hx₀ hcres

    have hac : a₀ * c = -b₀ := by
      rw [hc, hu.symm, mul_comm, mul_assoc, Units.inv_mul, mul_one]
    have hacQ : a * ((w : ℤ_[p]) : ℚ_[p]) ^ 2 = -b := by
      have h := congrArg (fun t : ℤ_[p] ↦ (t : ℚ_[p])) hac
      simp only [PadicInt.coe_mul, PadicInt.coe_neg] at h
      rw [← hw] at h
      simpa [ha₀, hb₀] using h
    refine ⟨0, (w : ℚ_[p]), 1, fun ⟨_, _, h1⟩ ↦ one_ne_zero h1, ?_⟩
    linear_combination -hacQ
  ·
    obtain ⟨xl, hxl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) x₀
    set c : ℤ_[p] := a₀ * xl ^ 2 + b₀ with hc
    have hcres : PadicInt.toZMod c = z₀ ^ 2 := by
      rw [hc, map_add, map_mul, map_pow, hxl]
      linear_combination -hzx
    obtain ⟨t, ht⟩ := exists_sq_eq_of_toZMod_eq_sq hp hz₀ hcres
    have htQ : ((t : ℤ_[p]) : ℚ_[p]) ^ 2 = a * ((xl : ℤ_[p]) : ℚ_[p]) ^ 2 + b := by
      have h := congrArg (fun s : ℤ_[p] ↦ (s : ℚ_[p])) ht
      simp only [PadicInt.coe_pow, hc, PadicInt.coe_add, PadicInt.coe_mul] at h
      simpa [ha₀, hb₀] using h
    refine ⟨(t : ℚ_[p]), (xl : ℚ_[p]), 1, fun ⟨_, _, h1⟩ ↦ one_ne_zero h1, ?_⟩
    linear_combination htQ
