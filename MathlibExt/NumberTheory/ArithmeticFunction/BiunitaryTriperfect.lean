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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Comparison bounds for biunitary divisor sums of prime powers

For a prime `p`, reindexing the biunitary divisor sum `σ**(p ^ e)` by the distance below the
highest exponent writes the normalized sum `σ**(p ^ e) / p ^ e` as a geometric progression with
at most the middle term omitted. At even exponent `2 * m` the omitted term is `1 / p ^ m`; at
any other exponent `e ≥ 2 * m - 1` the normalized sum dominates both the `2 * m` value and the
partial sum `∑ i ∈ range (m + 1), 1 / p ^ i`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3 (`jis-2025-25.4.5-lem-3`).
-/

namespace MetaMathlibExt

open Finset

namespace sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le

-- A prime power divisor is biunitary exactly off the middle exponent.
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

-- Every power up to the given exponent occurs except the middle one.
private theorem sigmaBiunitary_prime_pow_eq_sum {p g : ℕ} (hp : p.Prime) (hg : 0 < g) :
    sigmaBiunitary (p ^ g) = ∑ i ∈ range (g + 1), if 2 * i = g then 0 else p ^ i := by
  rw [sigmaBiunitary, biunitaryDivisors, sum_filter, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i hi
  simp [biunitary_pow_iff hp hg (Nat.le_of_lt_succ (mem_range.mp hi)), ite_not]

-- Reindex by the distance below the highest exponent; the normalized term is `1 / p ^ i`.
private theorem normalized {p g : ℕ} (hp : p.Prime) (hg : 0 < g) :
    (sigmaBiunitary (p ^ g) : ℚ) / (p : ℚ) ^ g =
      ∑ i ∈ range (g + 1), (if 2 * (g - i) = g then 0 else 1 / (p : ℚ) ^ i) := by
  have hne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [sigmaBiunitary_prime_pow_eq_sum hp hg, Nat.cast_sum, sum_div, ← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hie : i ≤ g := Nat.le_of_lt_succ (mem_range.mp hi)
  simp only [Nat.add_sub_cancel, Nat.cast_ite, Nat.cast_zero, Nat.cast_pow]
  by_cases h : 2 * (g - i) = g
  · simp only [h, ite_true, zero_div]
  · simp only [h, ite_false]
    apply (div_eq_div_iff (pow_ne_zero _ hne) (pow_ne_zero _ hne)).2
    rw [← pow_add, Nat.sub_add_cancel hie, one_mul]

-- Partial geometric sums over unomitted indices bound the normalized sum.
private theorem partial_le {p g : ℕ} (hp : p.Prime) (hg : 0 < g) (s : Finset ℕ)
    (hs : ∀ i ∈ s, i ≤ g ∧ 2 * (g - i) ≠ g) :
    ∑ i ∈ s, 1 / (p : ℚ) ^ i ≤ (sigmaBiunitary (p ^ g) : ℚ) / (p : ℚ) ^ g := by
  rw [normalized hp hg]
  calc ∑ i ∈ s, 1 / (p : ℚ) ^ i
      = ∑ i ∈ s, (if 2 * (g - i) = g then (0 : ℚ) else 1 / (p : ℚ) ^ i) :=
        sum_congr rfl fun i hi => by simp [(hs i hi).2]
    _ ≤ ∑ i ∈ range (g + 1), (if 2 * (g - i) = g then (0 : ℚ) else 1 / (p : ℚ) ^ i) :=
        sum_le_sum_of_subset_of_nonneg
          (fun i hi => mem_range.mpr (Nat.lt_succ_of_le (hs i hi).1))
          (fun i _ _ => by split <;> positivity)

-- At odd exponents no term is omitted.
private theorem normalized_of_odd {p g : ℕ} (hp : p.Prime) (hg : 0 < g) (hodd : Odd g) :
    (sigmaBiunitary (p ^ g) : ℚ) / (p : ℚ) ^ g =
      ∑ i ∈ range (g + 1), 1 / (p : ℚ) ^ i := by
  rw [normalized hp hg]
  refine sum_congr rfl fun i _ => ?_
  have h : 2 * (g - i) ≠ g := by
    intro hcon
    have heven : Even g := ⟨g - i, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  simp only [h, ite_false]

-- At even exponents exactly the middle term is omitted.
private theorem normalized_of_even {p g k : ℕ} (hp : p.Prime) (hg : g = 2 * k)
    (hk : 0 < k) :
    (sigmaBiunitary (p ^ g) : ℚ) / (p : ℚ) ^ g =
      (∑ i ∈ range (g + 1), 1 / (p : ℚ) ^ i) - 1 / (p : ℚ) ^ k := by
  have hgpos : 0 < g := by omega
  have hmem : k ∈ range (g + 1) := mem_range.mpr (by omega)
  have hsplit : ∀ i ∈ range (g + 1),
      (if 2 * (g - i) = g then (0 : ℚ) else 1 / (p : ℚ) ^ i) =
        1 / (p : ℚ) ^ i - (if i = k then 1 / (p : ℚ) ^ i else 0) := by
    intro i hi
    have hie : i ≤ g := Nat.le_of_lt_succ (mem_range.mp hi)
    by_cases hik : i = k
    · have hkk : 2 * (g - k) = g := by omega
      simp [hkk, hik]
    · have hkk : 2 * (g - i) ≠ g := by omega
      simp [hkk, hik]
  rw [normalized hp hgpos]
  calc ∑ i ∈ range (g + 1), (if 2 * (g - i) = g then (0 : ℚ) else 1 / (p : ℚ) ^ i)
      = ∑ i ∈ range (g + 1), (1 / (p : ℚ) ^ i - (if i = k then 1 / (p : ℚ) ^ i else 0)) :=
        sum_congr rfl hsplit
    _ = (∑ i ∈ range (g + 1), 1 / (p : ℚ) ^ i) -
          ∑ i ∈ range (g + 1), (if i = k then 1 / (p : ℚ) ^ i else 0) :=
        sum_sub_distrib _ _
    _ = (∑ i ∈ range (g + 1), 1 / (p : ℚ) ^ i) - 1 / (p : ℚ) ^ k := by
        simp [sum_ite_eq', hmem]

end sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le

open sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le

/-- **Comparison bounds for the biunitary divisor sum of a prime power.** Let $p$ be a prime and
let $m \ge 1$ and $e \ge 2m - 1$ be natural numbers, and write $\sigma^{**}$ for the biunitary
divisor sum. Then, in $\mathbb{Q}$,
$\sigma^{**}(p^e)/p^e \ge \sigma^{**}(p^{2m})/p^{2m}$, and if moreover $e \ne 2m$, then
$\sigma^{**}(p^e)/p^e \ge \sum_{i=0}^{m} 1/p^i$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3 (`jis-2025-25.4.5-lem-3`). -/
public theorem sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le (p m e : ℕ)
    (hp : p.Prime) (hm : 0 < m) (he : 2 * m - 1 ≤ e) :
    ((sigmaBiunitary (p ^ (2 * m)) : ℚ) / (p : ℚ) ^ (2 * m) ≤
        (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) ∧
      (e ≠ 2 * m → ∑ i ∈ Finset.range (m + 1), 1 / (p : ℚ) ^ i ≤
        (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hepos : 0 < e := by omega
  have hmain : (sigmaBiunitary (p ^ (2 * m)) : ℚ) / (p : ℚ) ^ (2 * m) =
      (∑ i ∈ range (2 * m + 1), 1 / (p : ℚ) ^ i) - 1 / (p : ℚ) ^ m :=
    normalized_of_even hp rfl hm
  constructor
  · by_cases hcase : e = 2 * m
    · subst hcase
      exact le_rfl
    · rcases Nat.even_or_odd e with hev | hodd
      · obtain ⟨k, hk⟩ := hev
        have hkpos : 0 < k := by omega
        have hke : e = 2 * k := by omega
        have heven : (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e =
            (∑ i ∈ range (e + 1), 1 / (p : ℚ) ^ i) - 1 / (p : ℚ) ^ k :=
          normalized_of_even hp hke hkpos
        have hsub : range (2 * m + 1) ⊆ range (e + 1) := by
          intro x hx
          simp only [mem_range] at hx ⊢
          omega
        have hfull : ∑ i ∈ range (2 * m + 1), 1 / (p : ℚ) ^ i ≤
            ∑ i ∈ range (e + 1), 1 / (p : ℚ) ^ i :=
          sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        have hpm : (0 : ℚ) < (p : ℚ) ^ m := by exact_mod_cast pow_pos hp.pos _
        have hle : (p : ℚ) ^ m ≤ (p : ℚ) ^ k := pow_le_pow_right₀ (by linarith) (by omega)
        have hpow : 1 / (p : ℚ) ^ k ≤ 1 / (p : ℚ) ^ m :=
          one_div_le_one_div_of_le hpm hle
        rw [hmain, heven]
        linarith
      · have hoddeq : (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e =
            ∑ i ∈ range (e + 1), 1 / (p : ℚ) ^ i :=
          normalized_of_odd hp hepos hodd
        by_cases hle : 2 * m ≤ e
        · have hsub : range (2 * m + 1) ⊆ range (e + 1) := by
            intro x hx
            simp only [mem_range] at hx ⊢
            omega
          have hfull : ∑ i ∈ range (2 * m + 1), 1 / (p : ℚ) ^ i ≤
              ∑ i ∈ range (e + 1), 1 / (p : ℚ) ^ i :=
            sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
          have hnonneg : (0 : ℚ) ≤ 1 / (p : ℚ) ^ m := by positivity
          rw [hmain, hoddeq]
          linarith
        · have heq1 : e + 1 = 2 * m := by omega
          have hpm : (0 : ℚ) < (p : ℚ) ^ m := by exact_mod_cast pow_pos hp.pos _
          have hle2 : (p : ℚ) ^ m ≤ (p : ℚ) ^ (2 * m) :=
            pow_le_pow_right₀ (by linarith) (by omega)
          have hpow : 1 / (p : ℚ) ^ (2 * m) ≤ 1 / (p : ℚ) ^ m :=
            one_div_le_one_div_of_le hpm hle2
          rw [hmain, hoddeq, heq1, sum_range_succ]
          linarith
  · intro hne
    refine partial_le hp hepos _ fun i hi => ?_
    have hi' : i < m + 1 := mem_range.mp hi
    refine ⟨by omega, by intro hcon; omega⟩

end MetaMathlibExt
