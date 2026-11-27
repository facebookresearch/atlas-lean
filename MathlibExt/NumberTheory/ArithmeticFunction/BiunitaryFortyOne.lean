/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.Order
import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution
import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowAddOne
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Biunitary divisor sums of prime powers

The biunitary divisors of a prime power are all powers from exponent zero to the given exponent,
except that the middle term is omitted when the given exponent is positive and even. We use this
description to bound the normalized sum and to find a prime factor of the sum for positive powers
of 41 outside `{2, 3, 5, 13}`.
-/

namespace MetaMathlibExt

open Finset

namespace exists_prime_dvd_sigmaBiunitary_fortyOne_pow

private theorem biunitary_pow_iff {p g i : ℕ} (hp : p.Prime) (hg : 0 < g) (hi : i ≤ g) :
    gcdUnitary (p ^ i) (p ^ g / p ^ i) = 1 ↔ 2 * i ≠ g := by
  rw [Nat.pow_div hi hp.pos]
  constructor
  · intro h hmid
    have he : g - i = i := by omega
    have hmem : p ^ i ∈ (p ^ i).unitaryDivisors := by simp [Nat.unitaryDivisors_prime_pow hp]
    rw [he] at h
    have hle := le_gcdUnitary hmem hmem
    rw [h] at hle
    exact (Nat.one_lt_pow (by omega : i ≠ 0) hp.one_lt).not_ge hle
  · intro hmid
    obtain ⟨h₁, h₂⟩ := gcdUnitary_mem_unitaryDivisors
      (pow_ne_zero i hp.ne_zero) (pow_ne_zero (g - i) hp.ne_zero)
    simp only [Nat.unitaryDivisors_prime_pow hp, mem_insert, mem_singleton] at h₁ h₂
    rcases h₁ with h | h
    · exact h
    rcases h₂ with h' | h'
    · exact h'
    have he := Nat.pow_right_injective hp.two_le (h.symm.trans h')
    omega

/-- Every power up to the given exponent occurs except the middle one. -/
private theorem sigmaBiunitary_prime_pow_eq_sum {p g : ℕ} (hp : p.Prime) (hg : 0 < g) :
    sigmaBiunitary (p ^ g) = ∑ i ∈ range (g + 1), if 2 * i = g then 0 else p ^ i := by
  rw [sigmaBiunitary, biunitaryDivisors, sum_filter, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i hi
  simp [biunitary_pow_iff hp hg (Nat.le_of_lt_succ (mem_range.mp hi)), ite_not]

-- Pair the lower block of exponents with its translate by n, skipping the middle when g is even.
private theorem pow_add_one_dvd_sum {p : ℕ} (hp : p.Prime) (g : ℕ) (hg : 0 < g) :
    p ^ (g / 2 + 1) + 1 ∣ sigmaBiunitary (p ^ g) := by
  let n := g / 2 + 1
  let k := (g + 1) / 2
  have hsplit : g + 1 = n + k := by dsimp [n, k]; omega
  have hblocks : n = k ∨ n = k + 1 := by dsimp [n, k]; omega
  let f (i : ℕ) := if 2 * i = g then 0 else p ^ i
  have hsum : sigmaBiunitary (p ^ g) = ∑ i ∈ range (g + 1), f i :=
    sigmaBiunitary_prime_pow_eq_sum hp hg
  have low : ∑ i ∈ range k, f i = ∑ i ∈ range k, p ^ i := by
    apply sum_congr rfl
    intro i hi
    have := mem_range.mp hi
    simp [f, show 2 * i ≠ g by omega]
  have lowBlock : ∑ i ∈ range n, f i = ∑ i ∈ range k, p ^ i := by
    rcases hblocks with h | h
    · rwa [h]
    · rw [h, sum_range_succ, low]
      simp [f, show 2 * k = g by omega]
  refine ⟨∑ i ∈ range k, p ^ i, ?_⟩
  change sigmaBiunitary (p ^ g) = (p ^ n + 1) * _
  rw [hsum, hsplit, sum_range_add, lowBlock, add_mul, one_mul, add_comm, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  simp [f, show 2 * (n + i) ≠ g by omega, pow_add]

private theorem prime_dvd_pow_add_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ q ∣ 41 ^ n + 1 ∧ q ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  by_cases hsmall : n ≤ 6
  · interval_cases n
    all_goals first
      | exact ⟨7, by decide, by decide, by decide⟩
      | exact ⟨29, by decide, by decide, by decide⟩
      | exact ⟨137, by decide, by decide, by decide⟩
  obtain ⟨q, hq, hmod⟩ := exists_primitivePrimeDivisor_pow_add_one 41 n (by decide) hn
    (by omega) (by omega)
  have hlarge : 13 < q := by
    by_contra! h
    rw [Nat.mod_eq_of_lt (by omega : q < 2 * n)] at hmod
    have := hq.two_le
    omega
  refine ⟨q, hq.prime, ?_, ?_⟩
  · exact_mod_cast hq.dvd
  · simp only [mem_insert, mem_singleton]
    omega

end exists_prime_dvd_sigmaBiunitary_fortyOne_pow

open exists_prime_dvd_sigmaBiunitary_fortyOne_pow

/-- **Prime factors of the biunitary divisor sum of $41^g$.** For every integer $g \ge 1$, the
biunitary divisor sum $\sigma^{**}(41^g)$ has a prime factor $q$ with $q \notin \{2, 3, 5, 13\}$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (V) (`jis-2025-25.4.5-lem-8`). -/
public theorem exists_prime_dvd_sigmaBiunitary_fortyOne_pow (g : ℕ) (hg : 1 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (41 ^ g) ∧ q ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  obtain ⟨q, hq, hdvd, hout⟩ := prime_dvd_pow_add_one (g / 2 + 1) (by omega)
  exact ⟨q, hq, hdvd.trans (pow_add_one_dvd_sum (by decide) g hg), hout⟩

/-- **Lower bounds for the biunitary divisor sum of a prime power.** Let $p$ be a prime and
$e \ge 1$, and write $\sigma^{**}$ for the biunitary divisor sum. Then, in $\mathbb{Q}$,
$\sigma^{**}(p^e)/p^e \ge 1 + 1/p^2$; if moreover $e \ne 2$, then
$\sigma^{**}(p^e)/p^e \ge 1 + 1/p$; and if $e \ge 3$, then
$\sigma^{**}(p^e)/p^e \ge (1 + 1/p)(1 + 1/p^3)$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3 (`jis-2025-25.4.5-lem-3`). -/
public theorem sigmaBiunitary_prime_pow_div_ge (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    (1 + 1 / (p : ℚ) ^ 2 ≤ (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) ∧
      (e ≠ 2 → 1 + 1 / (p : ℚ) ≤ (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) ∧
      (3 ≤ e → (1 + 1 / (p : ℚ)) * (1 + 1 / (p : ℚ) ^ 3) ≤
        (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℚ) < p := by linarith
  have hne : (p : ℚ) ≠ 0 := hpos.ne'
  -- Reindex by the distance below the highest exponent. Its normalized term is `1 / p ^ i`.
  let w (i : ℕ) : ℚ := if 2 * (e - i) = e then 0 else 1 / (p : ℚ) ^ i
  have hnormalized : (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e =
      ∑ i ∈ range (e + 1), w i := by
    rw [sigmaBiunitary_prime_pow_eq_sum hp he, Nat.cast_sum, sum_div, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have hie : i ≤ e := Nat.le_of_lt_succ (mem_range.mp hi)
    simp only [Nat.add_sub_cancel, Nat.cast_ite, Nat.cast_zero, Nat.cast_pow, w]
    split
    · simp
    · apply (div_eq_div_iff (pow_ne_zero _ hne) (pow_ne_zero _ hne)).2
      rw [← pow_add, Nat.sub_add_cancel hie, one_mul]
  have hpartial (s : Finset ℕ) (hs : ∀ i ∈ s, i ≤ e ∧ 2 * (e - i) ≠ e) :
      ∑ i ∈ s, 1 / (p : ℚ) ^ i ≤ (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e := by
    rw [hnormalized]
    calc
      _ = ∑ i ∈ s, w i := sum_congr rfl fun i hi => by simp [w, (hs i hi).2]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (fun i hi => mem_range.mpr (Nat.lt_succ_of_le (hs i hi).1))
        (fun i _ _ => by dsimp [w]; split <;> positivity)
  have htwo (he2 : e ≠ 2) : 1 + 1 / (p : ℚ) ≤ (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e := by
    simpa [Finset.sum_insert] using hpartial {0, 1} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> omega)
  refine ⟨?_, htwo, ?_⟩
  · by_cases h : e = 1 ∨ e = 4
    · apply le_trans _ (htwo (by omega))
      apply add_le_add (le_refl (1 : ℚ))
      rw [div_le_div_iff₀ (by positivity) hpos]
      nlinarith [sq_nonneg ((p : ℚ) - 2)]
    · simpa [Finset.sum_insert] using hpartial {0, 2} (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> omega)
  · intro he3
    have hexpand : (1 + 1 / (p : ℚ)) * (1 + 1 / (p : ℚ) ^ 3) =
        1 + 1 / (p : ℚ) + (1 / (p : ℚ) ^ 3 + 1 / (p : ℚ) ^ 4) := by
      field_simp [hne]
    rw [hexpand]
    by_cases he4 : e = 4
    · subst e
      simpa [Finset.sum_insert, add_assoc] using hpartial {0, 1, 3, 4} (by decide)
    · have hbound : 1 / (p : ℚ) ^ 3 + 1 / (p : ℚ) ^ 4 ≤ 1 / (p : ℚ) ^ 2 := by
        calc
          _ = ((p : ℚ) + 1) / (p : ℚ) ^ 4 := by field_simp [hne]
          _ ≤ _ := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hsq : (p : ℚ) + 1 ≤ (p : ℚ) ^ 2 := by
              nlinarith [sq_nonneg ((p : ℚ) - 2)]
            nlinarith only [mul_le_mul_of_nonneg_right hsq (sq_nonneg (p : ℚ))]
      apply le_trans (add_le_add (le_refl (1 + 1 / (p : ℚ))) hbound)
      simpa [Finset.sum_insert, add_assoc] using hpartial {0, 1, 2} (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> omega)

end MetaMathlibExt
