/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow.lean`
and
`P2M/Sol/S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow.lean`
and
`Theorems/Thm_PadicInt_dvd_of_one_add_prime_pow_eq_pow.lean`
and
`P2M/Sol/S_PadicInt_dvd_of_one_add_prime_pow_eq_pow.lean`
and
`Theorems/Thm_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one.lean`
and
`P2M/Sol/S_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one.lean`
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

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open PadicInt

private theorem exists_one_add_pow_eq_cubic {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ d : R, (1 + x) ^ n = 1 + n * x + (n.choose 2 : R) * x ^ 2 + x ^ 3 * d := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(n.choose 2 : R) + d + x * d, ?_⟩
    rw [pow_succ, hd, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    ring

private theorem exists_one_add_pow_eq_quadratic {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ c : R, (1 + x) ^ n = 1 + n * x + x ^ 2 * c := by
  obtain ⟨d, hd⟩ := exists_one_add_pow_eq_cubic x n
  exact ⟨(n.choose 2 : R) + x * d, by rw [hd]; ring⟩

variable {p : ℕ} [hp : Fact p.Prime]

private theorem toZMod_natCast_self : toZMod (p : ℤ_[p]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

private theorem toZModPow_natCast_self_pow (n : ℕ) :
    toZModPow n ((p : ℤ_[p]) ^ n) = 0 := by
  rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]

private theorem norm_eq_one_of_toZMod_ne_zero {z : ℤ_[p]} (hz : toZMod z ≠ 0) :
    ‖z‖ = 1 := by
  rcases lt_or_eq_of_le (norm_le_one z) with h | h
  · exfalso
    apply hz
    rw [← RingHom.mem_ker, ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits]
    exact h
  · exact h

private theorem norm_eq_one_of_toZMod_eq_one {z : ℤ_[p]} (hz : toZMod z = 1) :
    ‖z‖ = 1 :=
  norm_eq_one_of_toZMod_ne_zero (by rw [hz]; exact one_ne_zero)

private theorem exists_eq_one_add_prime_mul_of_toZMod_eq_one {z : ℤ_[p]}
    (hz : toZMod z = 1) : ∃ b : ℤ_[p], z = 1 + p * b := by
  have hker : z - 1 ∈ RingHom.ker (toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, hz, map_one, sub_self]
  rw [ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
  obtain ⟨b, hb⟩ := hker
  exact ⟨b, by rw [← hb]; ring⟩

private theorem toZMod_one_add_prime : toZMod (1 + p : ℤ_[p]) = 1 := by
  rw [map_add, map_one, toZMod_natCast_self, add_zero]

private theorem toZModPow_two_one_add_prime_pow (j : ℕ) :
    toZModPow 2 ((1 + p : ℤ_[p]) ^ j) = 1 + (j : ZMod (p ^ 2)) * p := by
  obtain ⟨c, hc⟩ := exists_one_add_pow_eq_quadratic (p : ℤ_[p]) j
  rw [hc, map_add, map_add, map_mul, map_one, map_mul, map_natCast, map_natCast,
    toZModPow_natCast_self_pow, zero_mul, add_zero]

private theorem toZModPow_two_pow_eq_one_of_toZMod_eq_one {z : ℤ_[p]}
    (hz : toZMod z = 1) : toZModPow 2 (z ^ p) = 1 := by
  obtain ⟨b, rfl⟩ := exists_eq_one_add_prime_mul_of_toZMod_eq_one hz
  obtain ⟨c, hc⟩ := exists_one_add_pow_eq_quadratic ((p : ℤ_[p]) * b) p
  have h : (1 + (p : ℤ_[p]) * b) ^ p = 1 + (p : ℤ_[p]) ^ 2 * (b + b ^ 2 * c) := by
    rw [hc]; ring
  rw [h, map_add, map_one, map_mul, toZModPow_natCast_self_pow, zero_mul, add_zero]

private theorem padicInt_dvd_of_one_add_prime_pow_eq_pow {j : ℕ} {z : ℤ_[p]}
    (h : (1 + p : ℤ_[p]) ^ j = z ^ p) : p ∣ j := by
  have hz1 : toZMod z = 1 := by
    have h' := congrArg toZMod h
    have hpow : (toZMod z) ^ p = toZMod z := by
      have hcard := FiniteField.pow_card (K := ZMod p) (toZMod z)
      rwa [ZMod.card p] at hcard
    rw [map_pow, toZMod_one_add_prime, one_pow, map_pow, hpow] at h'
    exact h'.symm
  have h2 := toZModPow_two_pow_eq_one_of_toZMod_eq_one hz1
  rw [← h, toZModPow_two_one_add_prime_pow, add_eq_left, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff, pow_two] at h2
  exact Nat.dvd_of_mul_dvd_mul_right hp.out.pos h2

open Padic in
private theorem natCast_prime_ne_zero : ((p : ℚ_[p])) ≠ 0 :=
  Nat.cast_ne_zero.mpr hp.out.ne_zero

private theorem coe_one_add_prime : ((1 + p : ℤ_[p]) : ℚ_[p]) = 1 + p := by
  push_cast; rfl

private theorem norm_one_add_prime : ‖(1 + p : ℚ_[p])‖ = 1 := by
  rw [← coe_one_add_prime]
  exact norm_eq_one_of_toZMod_eq_one toZMod_one_add_prime

private theorem one_add_prime_ne_zero : (1 + p : ℚ_[p]) ≠ 0 := by
  intro h
  have h1 := norm_one_add_prime (p := p)
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

private theorem valuation_eq_zero_of_norm_eq_one {u : ℚ_[p]} (hu : ‖u‖ = 1) :
    u.valuation = 0 := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact one_ne_zero hu.symm
  have h := Padic.norm_eq_zpow_neg_valuation hu0
  rw [hu] at h
  have hbase0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hbase1 : ((p : ℝ)) ≠ 1 := by exact_mod_cast hp.out.one_lt.ne'
  have := (zpow_right_inj₀ hbase0 hbase1).mp (h.symm.trans (zpow_zero _).symm)
  omega

private theorem norm_eq_one_of_norm_pow_eq_one {y : ℚ_[p]} {n : ℕ} (hn : n ≠ 0)
    (h : ‖y ^ n‖ = 1) : ‖y‖ = 1 := by
  rw [norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg y) hn).mp h

private theorem dvd_of_one_add_prime_pow_eq_pow_rat {n : ℕ} {w : ℚ_[p]}
    (h : (1 + p : ℚ_[p]) ^ n = w ^ p) : p ∣ n := by
  have hw : ‖w‖ = 1 :=
    norm_eq_one_of_norm_pow_eq_one hp.out.ne_zero
      (by rw [← h, norm_pow, norm_one_add_prime, one_pow])
  set wInt : ℤ_[p] := ⟨w, le_of_eq hw⟩ with hwInt_def
  have hInt : (1 + p : ℤ_[p]) ^ n = wInt ^ p := by
    apply Subtype.ext
    push_cast [hwInt_def]
    exact h
  exact padicInt_dvd_of_one_add_prime_pow_eq_pow hInt

private theorem dvd_of_one_add_prime_zpow_eq_pow {j : ℤ} {w : ℚ_[p]}
    (h : (1 + p : ℚ_[p]) ^ j = w ^ p) : (p : ℤ) ∣ j := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = n ∨ j = -n := ⟨j.natAbs, Int.natAbs_eq j⟩
  rcases hn with rfl | rfl
  · rw [zpow_natCast] at h
    exact Int.natCast_dvd_natCast.mpr (dvd_of_one_add_prime_pow_eq_pow_rat h)
  · rw [dvd_neg]
    refine Int.natCast_dvd_natCast.mpr
      (dvd_of_one_add_prime_pow_eq_pow_rat (w := w⁻¹) ?_)
    rw [inv_pow, ← h, zpow_neg, zpow_natCast, inv_inv]

namespace Padic

/-- If a product of an integral power of `p` and an integral power of `1 + p`
in `ℚ_[p]` is a `p`-th power, then `p` divides both exponents. -/
public theorem dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow {p : ℕ} [Fact p.Prime]
    {i j : ℤ} {y : ℚ_[p]}
    (h : (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j = y ^ p) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  have hval : i = p * y.valuation := by
    have h1 : ((p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j).valuation = i := by
      rw [Padic.valuation_mul (zpow_ne_zero _ natCast_prime_ne_zero)
          (zpow_ne_zero _ one_add_prime_ne_zero),
        Padic.valuation_zpow, Padic.valuation_zpow,
        valuation_eq_zero_of_norm_eq_one norm_one_add_prime,
        mul_zero, add_zero, Padic.valuation_p, mul_one]
    rw [h, Padic.valuation_pow] at h1
    exact h1.symm
  have hi : (p : ℤ) ∣ i := ⟨y.valuation, hval⟩
  refine ⟨hi, ?_⟩
  obtain ⟨q, hq⟩ := hi
  have e3 : ((p : ℚ_[p]) ^ (-q)) ^ p = ((p : ℚ_[p]) ^ i)⁻¹ := by
    rw [← zpow_natCast ((p : ℚ_[p]) ^ (-q)), ← zpow_mul, neg_mul, zpow_neg, hq, mul_comm]
  refine dvd_of_one_add_prime_zpow_eq_pow (w := y * (p : ℚ_[p]) ^ (-q)) ?_
  calc (1 + p : ℚ_[p]) ^ j
      = ((p : ℚ_[p]) ^ i)⁻¹ * ((p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j) := by
        rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ natCast_prime_ne_zero), one_mul]
    _ = ((p : ℚ_[p]) ^ i)⁻¹ * y ^ p := by rw [h]
    _ = (y * (p : ℚ_[p]) ^ (-q)) ^ p := by rw [mul_pow, e3]; ring

end Padic
