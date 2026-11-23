/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
`Theorems/Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg.lean` and
`P2M/Sol/S_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg.lean`,
together with the integer and natural-number valuation lemmas they build on.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib (https://github.com/leanprover-community/mathlib4):
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

import Mathlib.Data.Int.GCD
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Rational membership in a valuation subring

A nonzero rational number lies in a valuation subring of a characteristic-zero
field exactly when its `q`-adic valuation is nonnegative, provided the
valuation of `q` itself is less than one.
-/

@[expose] public section

namespace ValuationSubring

private theorem valuation_natCast_eq_one_of_not_dvd {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {n : ℕ} (hqn : ¬q ∣ n) : A.valuation (n : K) = 1 := by
  have hleZ : ∀ a : ℤ, A.valuation (a : K) ≤ 1 := fun a =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  have hle : ∀ m : ℕ, A.valuation (m : K) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (natCast_mem A m)
  refine le_antisymm (hle n) ?_
  by_contra hlt
  have hnlt : A.valuation (n : K) < 1 := lt_of_le_of_ne (hle n) (fun h => hlt h.ge)
  have hcop : Nat.Coprime q n := (hq.coprime_iff_not_dvd).mpr hqn
  have hbez : ((Nat.gcd q n : ℤ) : K)
      = (q : K) * ((Nat.gcdA q n : ℤ) : K) + (n : K) * ((Nat.gcdB q n : ℤ) : K) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : K)) (Nat.gcd_eq_gcd_ab q n)
  rw [hcop.gcd_eq_one] at hbez
  push_cast at hbez
  have h1 : A.valuation 1
      ≤ max (A.valuation ((q : K) * ((Nat.gcdA q n : ℤ) : K)))
          (A.valuation ((n : K) * ((Nat.gcdB q n : ℤ) : K))) := by
    rw [show (1 : K) = (q : K) * ((Nat.gcdA q n : ℤ) : K)
        + (n : K) * ((Nat.gcdB q n : ℤ) : K) from hbez]
    exact A.valuation.map_add _ _
  have hterm1 : A.valuation ((q : K) * ((Nat.gcdA q n : ℤ) : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (q : K) * A.valuation ((Nat.gcdA q n : ℤ) : K)
        ≤ A.valuation (q : K) * 1 := mul_le_mul' le_rfl (hleZ _)
      _ = A.valuation (q : K) := mul_one _
      _ < 1 := hA
  have hterm2 : A.valuation ((n : K) * ((Nat.gcdB q n : ℤ) : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (n : K) * A.valuation ((Nat.gcdB q n : ℤ) : K)
        ≤ A.valuation (n : K) * 1 := mul_le_mul' le_rfl (hleZ _)
      _ = A.valuation (n : K) := mul_one _
      _ < 1 := hnlt
  rw [map_one] at h1
  exact absurd h1 (not_le.mpr (max_lt hterm1 hterm2))

private theorem valuation_intCast_eq_one_of_not_dvd {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {a : ℤ} (hqa : ¬(q : ℤ) ∣ a) : A.valuation (a : K) = 1 := by
  have hn : ¬q ∣ a.natAbs := fun h => hqa (Int.natCast_dvd.mpr h)
  have h1 := A.valuation_natCast_eq_one_of_not_dvd hq hA hn
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.cast_natCast]; exact h1
  · rw [h, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact h1

private theorem valuation_intCast_eq_pow_padicValInt {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {z : ℤ} (hz : z ≠ 0) : A.valuation (z : K) = A.valuation (q : K) ^ padicValInt q z := by
  haveI : Fact q.Prime := ⟨hq⟩
  set v : ℕ := multiplicity q z.natAbs with hv
  have hn0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hdvd : q ^ v ∣ z.natAbs := pow_multiplicity_dvd q z.natAbs
  obtain ⟨c, hc⟩ := hdvd
  have hqc : ¬(q : ℤ) ∣ (c : ℤ) := by
    intro h
    have h' : q ∣ c := Int.natCast_dvd_natCast.mp h
    obtain ⟨d, rfl⟩ := h'
    have : q ^ (v + 1) ∣ z.natAbs := ⟨d, by rw [hc]; ring⟩
    exact pow_succ_multiplicity_not_dvd hn0 this
  have hcval : A.valuation ((c : ℤ) : K) = 1 :=
    A.valuation_intCast_eq_one_of_not_dvd hq hA hqc
  have habs : A.valuation (z : K) = A.valuation ((z.natAbs : ℤ) : K) := by
    rcases Int.natAbs_eq z with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg]
  have hpv : padicValInt q z = v := rfl
  rw [habs, hpv, Int.cast_natCast, hc, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow,
    show ((c : ℕ) : K) = ((c : ℤ) : K) by norm_cast, hcval, mul_one]

private theorem valuation_ratCast_eq_zpow_padicValRat {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) :
    A.valuation (r : K) = A.valuation (q : K) ^ padicValRat q r := by
  have hnum : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  have hden : (r.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr r.den_nz
  have hq0 : A.valuation (q : K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hq.ne_zero)
  have hcast : (r : K) = (r.num : K) / ((r.den : ℤ) : K) := by
    rw [Rat.cast_def]; push_cast; rfl
  rw [hcast, map_div₀, A.valuation_intCast_eq_pow_padicValInt hq hA hnum,
    A.valuation_intCast_eq_pow_padicValInt hq hA hden, padicValRat_def,
    padicValInt.of_nat, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]

private theorem zpow_facts {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {g : Γ}
    (hg0 : g ≠ 0) (hg1 : g < 1) (k : ℤ) :
    (g ^ k ≤ 1 ↔ 0 ≤ k) ∧ (g ^ k = 1 ↔ k = 0) ∧ (g ^ k < 1 ↔ 0 < k) := by
  have hpos : ∀ n : ℕ, 0 < n → g ^ (n : ℤ) < 1 := fun n hn => by
    rw [zpow_natCast]; exact pow_lt_one₀ zero_le hg1 (Nat.pos_iff_ne_zero.mp hn)
  have hneg : ∀ n : ℕ, 0 < n → 1 < g ^ (-(n : ℤ)) := fun n hn => by
    rw [zpow_neg, zpow_natCast]
    exact one_lt_inv_iff₀.mpr ⟨pow_pos (zero_lt_iff.mpr hg0) n,
      pow_lt_one₀ zero_le hg1 (Nat.pos_iff_ne_zero.mp hn)⟩
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h := hpos n hn
      refine ⟨⟨fun _ => by exact_mod_cast hn.le, fun _ => h.le⟩,
        ⟨fun h1 => absurd h1 h.ne, fun h0 => ?_⟩,
        ⟨fun _ => by exact_mod_cast hn, fun _ => h⟩⟩
      exact absurd h0 (by exact_mod_cast hn.ne')
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h := hneg n hn
      have hk : ¬(0 : ℤ) ≤ -(n : ℤ) := by omega
      have hk' : ¬(0 : ℤ) < -(n : ℤ) := by omega
      have hk'' : (-(n : ℤ)) ≠ 0 := by omega
      exact ⟨⟨fun h1 => absurd h1 (not_le.mpr h), fun h0 => absurd h0 hk⟩,
        ⟨fun h1 => absurd h1 h.ne', fun h0 => absurd h0 hk''⟩,
        ⟨fun h1 => absurd h1 (not_lt.mpr h.le), fun h0 => absurd h0 hk'⟩⟩

/-- A nonzero rational lies in a valuation subring of a characteristic-zero
field exactly when its `q`-adic valuation is nonnegative, provided the
valuation of the prime `q` is less than one. -/
public theorem ratCast_mem_iff_padicValRat_nonneg {K : Type*} [Field K] [CharZero K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {r : ℚ} (hr : r ≠ 0) : (r : K) ∈ A ↔ 0 ≤ padicValRat q r := by
  have hq0 : A.valuation (q : K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hq.ne_zero)
  rw [← A.valuation_le_one_iff, A.valuation_ratCast_eq_zpow_padicValRat hq hA hr]
  exact (zpow_facts hq0 hA _).1

end ValuationSubring
