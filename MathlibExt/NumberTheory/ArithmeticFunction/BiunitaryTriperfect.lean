/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisorParity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryFortyOne
import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution
import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowAddOne

/-!
# Biunitary divisor sums and biunitary triperfect numbers

## Main statements

* `sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le`: for a prime `p` and natural numbers
  `m ≥ 1` and `e ≥ 2 * m - 1`, the normalized sum `σ**(p ^ e) / p ^ e` is at least
  `σ**(p ^ (2 * m)) / p ^ (2 * m)`, and, if `e ≠ 2 * m`, at least
  `∑ i ∈ range (m + 1), 1 / p ^ i`. Reindexing `σ**(p ^ e)` by the distance below the highest
  exponent writes the normalized sum as a geometric progression with at most the middle term
  omitted.
* `two_pow_card_primeFactors_dvd_sigmaBiunitary_of_odd`: for every odd natural number `n`,
  `2 ^ ω(n)` divides `σ**(n)`, where `ω(n)` is the number of distinct prime factors of `n`. The
  biunitary divisor sum is multiplicative, and its value at an odd prime power is even.
* `four_le_factorization_two_of_biunitaryTriperfect`: a positive integer `N` with `σ**(N) = 3N`
  and `3 ≤ N.factorization 3` satisfies `4 ≤ N.factorization 2`.
* `eq_2160_of_factorization_two_eq_four`: a positive integer `N` with `σ**(N) = 3N`, exact
  exponent four at two and exponent three or four at three equals `2160` (Lemma 14). After
  removing the factor `2 ^ 4`, the multiplicativity of `σ**` and the parity of `σ**` at odd
  prime powers leave only `N = 2 ^ 4 * 3 ^ 3 * 5`.

Here `σ**` is the biunitary divisor sum.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemmas 2, 3 and 9.
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

private theorem ne_zero_of_dvd_ne_zero {d m : ℕ} (hd : d ∣ m) (hm : m ≠ 0) : d ≠ 0 := by
  rintro rfl
  obtain ⟨k, hk⟩ := hd
  exact hm (by simpa using hk)

private theorem div_ne_zero_of_dvd {d m : ℕ} (hd : d ∣ m) (hm : m ≠ 0) : m / d ≠ 0 := by
  intro h
  apply hm
  rw [← Nat.div_mul_cancel hd, h, zero_mul]

private theorem gcd_mul_gcd_eq_of_dvd_mul {d m n : ℕ} (hmn : m.Coprime n)
    (hd : d ∣ m * n) : d.gcd m * d.gcd n = d := by
  rw [← Nat.Coprime.gcd_mul d hmn, Nat.gcd_eq_left hd]

private theorem gcdUnitary_eq_one_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b = 1 ↔ ∀ u ∈ a.unitaryDivisors ∩ b.unitaryDivisors, u = 1 := by
  constructor
  · intro h u hu
    obtain ⟨hua, hub⟩ := mem_inter.mp hu
    have hle := le_gcdUnitary hua hub
    rw [h] at hle
    have hu0 : u ≠ 0 :=
      ne_zero_of_dvd_ne_zero (Nat.dvd_of_mem_unitaryDivisors hua) ha
    omega
  · intro h
    have h1mem : 1 ∈ a.unitaryDivisors ∩ b.unitaryDivisors :=
      mem_inter.mpr ⟨by simp [ha], by simp [hb]⟩
    simp only [gcdUnitary]
    apply le_antisymm
    · apply Finset.sup_le
      intro u hu
      rw [h u hu]
      exact le_refl 1
    · simpa using Finset.le_sup (f := id) h1mem

private theorem mul_mem_inter_unitaryDivisors {d1 e1 d2 e2 u1 u2 : ℕ}
    (h12d : d1.Coprime d2) (h12e : e1.Coprime e2)
    (h1 : u1 ∈ d1.unitaryDivisors ∩ e1.unitaryDivisors)
    (h2 : u2 ∈ d2.unitaryDivisors ∩ e2.unitaryDivisors) :
    u1 * u2 ∈ (d1 * d2).unitaryDivisors ∩ (e1 * e2).unitaryDivisors := by
  rw [mem_inter] at h1 h2 ⊢
  exact ⟨Nat.mul_mem_unitaryDivisors_mul h12d h1.1 h2.1,
    Nat.mul_mem_unitaryDivisors_mul h12e h1.2 h2.2⟩

private theorem gcd_mem_inter_unitaryDivisors {m n d1 d2 e1 e2 u : ℕ} (hmn : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd1 : d1 ∣ m) (hd2 : d2 ∣ n) (he1 : e1 ∣ m) (he2 : e2 ∣ n)
    (hu : u ∈ (d1 * d2).unitaryDivisors ∩ (e1 * e2).unitaryDivisors) :
    u.gcd m ∈ d1.unitaryDivisors ∩ e1.unitaryDivisors ∧
      u.gcd n ∈ d2.unitaryDivisors ∩ e2.unitaryDivisors ∧ u.gcd m * u.gcd n = u := by
  obtain ⟨hud, hue⟩ := mem_inter.mp hu
  have huDdvd : u ∣ d1 * d2 := Nat.dvd_of_mem_unitaryDivisors hud
  have huEdvd : u ∣ e1 * e2 := Nat.dvd_of_mem_unitaryDivisors hue
  have huDcop : u.Coprime ((d1 * d2) / u) := Nat.coprime_div_of_mem_unitaryDivisors hud
  have huEcop : u.Coprime ((e1 * e2) / u) := Nat.coprime_div_of_mem_unitaryDivisors hue
  have hu1m : u.gcd m ∣ m := Nat.gcd_dvd_right u m
  have hu2n : u.gcd n ∣ n := Nat.gcd_dvd_right u n
  have hu1u : u.gcd m ∣ u := Nat.gcd_dvd_left u m
  have hu2u : u.gcd n ∣ u := Nat.gcd_dvd_left u n
  have hc1d2 : (u.gcd m).Coprime d2 := (hmn.coprime_dvd_left hu1m).coprime_dvd_right hd2
  have hc1e2 : (u.gcd m).Coprime e2 := (hmn.coprime_dvd_left hu1m).coprime_dvd_right he2
  have hc2d1 : (u.gcd n).Coprime d1 :=
    (hmn.symm.coprime_dvd_left hu2n).coprime_dvd_right hd1
  have hc2e1 : (u.gcd n).Coprime e1 :=
    (hmn.symm.coprime_dvd_left hu2n).coprime_dvd_right he1
  have hu1d1 : u.gcd m ∣ d1 := hc1d2.dvd_of_dvd_mul_right (hu1u.trans huDdvd)
  have hu2d2 : u.gcd n ∣ d2 := hc2d1.dvd_of_dvd_mul_left (hu2u.trans huDdvd)
  have hu1e1 : u.gcd m ∣ e1 := hc1e2.dvd_of_dvd_mul_right (hu1u.trans huEdvd)
  have hu2e2 : u.gcd n ∣ e2 := hc2e1.dvd_of_dvd_mul_left (hu2u.trans huEdvd)
  have humn : u ∣ m * n := huDdvd.trans (Nat.mul_dvd_mul hd1 hd2)
  have hsplit : u.gcd m * u.gcd n = u := gcd_mul_gcd_eq_of_dvd_mul hmn humn
  have hqd : (d1 * d2) / u = d1 / u.gcd m * (d2 / u.gcd n) := by
    conv_lhs => rw [← hsplit]
    exact (Nat.div_mul_div_comm hu1d1 hu2d2).symm
  have hqe : (e1 * e2) / u = e1 / u.gcd m * (e2 / u.gcd n) := by
    conv_lhs => rw [← hsplit]
    exact (Nat.div_mul_div_comm hu1e1 hu2e2).symm
  rw [hqd] at huDcop
  rw [hqe] at huEcop
  have hc1d : (u.gcd m).Coprime (d1 / u.gcd m) :=
    (huDcop.coprime_dvd_left hu1u).coprime_dvd_right (Nat.dvd_mul_right _ _)
  have hc2d : (u.gcd n).Coprime (d2 / u.gcd n) :=
    (huDcop.coprime_dvd_left hu2u).coprime_dvd_right (Nat.dvd_mul_left _ _)
  have hc1e : (u.gcd m).Coprime (e1 / u.gcd m) :=
    (huEcop.coprime_dvd_left hu1u).coprime_dvd_right (Nat.dvd_mul_right _ _)
  have hc2e : (u.gcd n).Coprime (e2 / u.gcd n) :=
    (huEcop.coprime_dvd_left hu2u).coprime_dvd_right (Nat.dvd_mul_left _ _)
  have hd10 : d1 ≠ 0 := ne_zero_of_dvd_ne_zero hd1 hm
  have hd20 : d2 ≠ 0 := ne_zero_of_dvd_ne_zero hd2 hn
  have he10 : e1 ≠ 0 := ne_zero_of_dvd_ne_zero he1 hm
  have he20 : e2 ≠ 0 := ne_zero_of_dvd_ne_zero he2 hn
  refine ⟨mem_inter.mpr ⟨?_, ?_⟩, mem_inter.mpr ⟨?_, ?_⟩, hsplit⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu1d1, hd10, hc1d⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu1e1, he10, hc1e⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu2d2, hd20, hc2d⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu2e2, he20, hc2e⟩

private theorem gcd_mem_biunitaryDivisors_of_mem_mul_left {m n d : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hmn : m.Coprime n) (hd : d ∈ biunitaryDivisors (m * n)) :
    d.gcd m ∈ biunitaryDivisors m := by
  obtain ⟨hdvd, hmn0, hunit⟩ := mem_biunitaryDivisors.mp hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hdvd hmn0
  have hd1 : d.gcd m ∣ m := Nat.gcd_dvd_right d m
  have hd2 : d.gcd n ∣ n := Nat.gcd_dvd_right d n
  have hd10 : d.gcd m ≠ 0 := ne_zero_of_dvd_ne_zero hd1 hm
  have hd20 : d.gcd n ≠ 0 := ne_zero_of_dvd_ne_zero hd2 hn
  have he10 : m / d.gcd m ≠ 0 := div_ne_zero_of_dvd hd1 hm
  have he20 : n / d.gcd n ≠ 0 := div_ne_zero_of_dvd hd2 hn
  have hsplit : d.gcd m * d.gcd n = d := gcd_mul_gcd_eq_of_dvd_mul hmn hdvd
  have hqsplit : m / d.gcd m * (n / d.gcd n) = m * n / d := by
    rw [Nat.div_mul_div_comm hd1 hd2, hsplit]
  have hquot0 : m * n / d ≠ 0 := div_ne_zero_of_dvd hdvd hmn0
  refine mem_biunitaryDivisors.mpr ⟨hd1, hm, ?_⟩
  rw [gcdUnitary_eq_one_iff hd10 he10]
  intro u1 hu1
  have h1mem : (1 : ℕ) ∈ (d.gcd n).unitaryDivisors ∩ (n / d.gcd n).unitaryDivisors :=
    mem_inter.mpr ⟨by simp [hd20], by simp [he20]⟩
  have hprod := mul_mem_inter_unitaryDivisors
    ((hmn.coprime_dvd_left hd1).coprime_dvd_right hd2)
    ((hmn.coprime_dvd_left (Nat.div_dvd_of_dvd hd1)).coprime_dvd_right
      (Nat.div_dvd_of_dvd hd2))
    hu1 h1mem
  rw [hsplit, hqsplit, mul_one] at hprod
  exact (gcdUnitary_eq_one_iff hd0 hquot0).mp hunit _ hprod

private theorem gcd_mem_biunitaryDivisors_of_mem_mul_right {m n d : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hmn : m.Coprime n) (hd : d ∈ biunitaryDivisors (m * n)) :
    d.gcd n ∈ biunitaryDivisors n := by
  rw [mul_comm m n] at hd
  exact gcd_mem_biunitaryDivisors_of_mem_mul_left hn hm hmn.symm hd

private theorem mul_mem_biunitaryDivisors_mul {m n d1 d2 : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) (h1 : d1 ∈ biunitaryDivisors m) (h2 : d2 ∈ biunitaryDivisors n) :
    d1 * d2 ∈ biunitaryDivisors (m * n) := by
  obtain ⟨hd1, -, hunit1⟩ := mem_biunitaryDivisors.mp h1
  obtain ⟨hd2, -, hunit2⟩ := mem_biunitaryDivisors.mp h2
  have hdvd : d1 * d2 ∣ m * n := Nat.mul_dvd_mul hd1 hd2
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  have hd0 : d1 * d2 ≠ 0 := ne_zero_of_dvd_ne_zero hdvd hmn0
  have hq : m * n / (d1 * d2) = m / d1 * (n / d2) :=
    (Nat.div_mul_div_comm hd1 hd2).symm
  have hquot0 : m * n / (d1 * d2) ≠ 0 := div_ne_zero_of_dvd hdvd hmn0
  have hd10 : d1 ≠ 0 := ne_zero_of_dvd_ne_zero hd1 hm
  have he10 : m / d1 ≠ 0 := div_ne_zero_of_dvd hd1 hm
  have hd20 : d2 ≠ 0 := ne_zero_of_dvd_ne_zero hd2 hn
  have he20 : n / d2 ≠ 0 := div_ne_zero_of_dvd hd2 hn
  refine mem_biunitaryDivisors.mpr ⟨hdvd, hmn0, ?_⟩
  rw [gcdUnitary_eq_one_iff hd0 hquot0, hq]
  intro u hu
  obtain ⟨hu1, hu2, hsplit⟩ := gcd_mem_inter_unitaryDivisors hmn hm hn hd1 hd2
    (Nat.div_dvd_of_dvd hd1) (Nat.div_dvd_of_dvd hd2) hu
  have e1 := (gcdUnitary_eq_one_iff hd10 he10).mp hunit1 _ hu1
  have e2 := (gcdUnitary_eq_one_iff hd20 he20).mp hunit2 _ hu2
  rw [e1, e2, mul_one] at hsplit
  exact hsplit.symm

private theorem sigmaBiunitary_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    sigmaBiunitary (m * n) = sigmaBiunitary m * sigmaBiunitary n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [sigmaBiunitary]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 * x.2) (fun d => (d.gcd m, d.gcd n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    rw [mem_product] at hab
    exact mul_mem_biunitaryDivisors_mul hm hn hmn hab.1 hab.2
  · intro d hd
    rw [mem_product]
    exact ⟨gcd_mem_biunitaryDivisors_of_mem_mul_left hm hn hmn hd,
      gcd_mem_biunitaryDivisors_of_mem_mul_right hm hn hmn hd⟩
  · rintro ⟨a, b⟩ hab
    rw [mem_product] at hab
    have ha : a ∣ m := dvd_of_mem_biunitaryDivisors hab.1
    have hb : b ∣ n := dvd_of_mem_biunitaryDivisors hab.2
    have hbm : b.Coprime m := hmn.symm.coprime_dvd_left hb
    have han : a.Coprime n := hmn.coprime_dvd_left ha
    change ((a * b).gcd m, (a * b).gcd n) = (a, b)
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ha],
      by rw [mul_comm a b, Nat.Coprime.gcd_mul_right_cancel b han, Nat.gcd_eq_left hb]⟩
  · intro d hd
    exact gcd_mul_gcd_eq_of_dvd_mul hmn (dvd_of_mem_biunitaryDivisors hd)
  · rintro ⟨a, b⟩ _
    rfl

/-- **Powers of two dividing the biunitary divisor sum of an odd number.** For every odd natural
number $n$, $2^{\omega(n)}$ divides $\sigma^{**}(n)$, where $\omega(n)$ is the number of distinct
prime factors of $n$ and $\sigma^{**}$ is the biunitary divisor sum.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem two_pow_card_primeFactors_dvd_sigmaBiunitary_of_odd (n : ℕ)
    (hn : Odd n) : 2 ^ n.primeFactors.card ∣ sigmaBiunitary n := by
  have hn0 : n ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hn)
  have hmul : ∀ x y : ℕ, x.Coprime y →
      sigmaBiunitary (x * y) = sigmaBiunitary x * sigmaBiunitary y :=
    fun x y h => sigmaBiunitary_mul_of_coprime h
  have hfact : sigmaBiunitary n = n.factorization.prod fun p k => sigmaBiunitary (p ^ k) :=
    Nat.multiplicative_factorization sigmaBiunitary hmul sigmaBiunitary_one hn0
  rw [hfact]
  change 2 ^ n.primeFactors.card ∣ ∏ p ∈ n.primeFactors, sigmaBiunitary (p ^ n.factorization p)
  have h2 : (2 : ℕ) ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 :=
    (Finset.prod_const 2).symm
  rw [h2]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
  change 2 ∣ sigmaBiunitary (p ^ n.factorization p)
  obtain ⟨hpprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have hodd_p : Odd p := by
    obtain ⟨a, rfl⟩ := hpdvd
    exact Nat.Odd.of_mul_left hn
  have he : 1 ≤ n.factorization p := hpprime.factorization_pos_of_dvd hn0 hpdvd
  have hpos : 0 < p ^ n.factorization p := pow_pos hpprime.pos _
  rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
  intro hodd
  obtain ⟨k, hk⟩ := (odd_sigmaBiunitary_iff _ hpos).mp hodd
  have hodd_pow : Odd (p ^ n.factorization p) := hodd_p.pow
  rw [hk] at hodd_pow
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    have hlt : 1 < p ^ n.factorization p := Nat.one_lt_pow (by omega) hpprime.one_lt
    omega
  · exact hodd_pow.not_two_dvd_nat (dvd_pow_self 2 hk0.ne')

private theorem sigmaBiunitary_two : sigmaBiunitary 2 = 3 := by decide

private theorem sigmaBiunitary_eight : sigmaBiunitary 8 = 15 := by decide

private theorem sigmaBiunitary_twentyFive : sigmaBiunitary 25 = 26 := by decide

private theorem sigmaBiunitary_thirteen : sigmaBiunitary 13 = 14 := by decide

private theorem sigmaBiunitary_oneSixtyNine : sigmaBiunitary 169 = 170 := by decide

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

private theorem sigmaBiunitary_prime_pow_mod {p g : ℕ} (hp : p.Prime) (hg : 1 ≤ g) :
    sigmaBiunitary (p ^ g) % p = 1 := by
  have hsum := sigmaBiunitary_prime_pow_eq_sum hp (by omega : 0 < g)
  have h0 : (if 2 * 0 = g then (0 : ℕ) else p ^ 0) = 1 := by simp [show (0 : ℕ) ≠ g by omega]
  have hrest : p ∣ ∑ i ∈ range (g + 1) \ {0}, (if 2 * i = g then (0 : ℕ) else p ^ i) := by
    apply dvd_sum
    intro i hi
    simp only [mem_sdiff, mem_range, mem_singleton] at hi
    by_cases hmid : 2 * i = g
    · simp [hmid]
    · simp only [hmid, ite_false]
      exact dvd_pow_self p (by omega : i ≠ 0)
  have hmem : (0 : ℕ) ∈ range (g + 1) := mem_range.mpr (by omega)
  have hsplit := Finset.add_sum_erase (range (g + 1))
    (fun i => if 2 * i = g then (0 : ℕ) else p ^ i) hmem
  rw [sdiff_singleton_eq_erase] at hrest
  obtain ⟨T, hT⟩ := hrest
  rw [hsum, ← hsplit, h0, hT, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hp.one_lt

private theorem even_sigmaBiunitary_of_odd_pos {m : ℕ} (hm : Odd m) (hm1 : 1 < m) :
    Even (sigmaBiunitary m) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  rw [odd_sigmaBiunitary_iff m (by omega : 0 < m)] at hodd
  obtain ⟨k, hk⟩ := hodd
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp at hk
    omega
  · exact hm.not_two_dvd_nat (hk ▸ dvd_pow_self 2 (by omega : k ≠ 0))

private theorem self_mem_biunitaryDivisors {n : ℕ} (hn : 1 ≤ n) :
    n ∈ biunitaryDivisors n := by
  have hn0 : n ≠ 0 := by omega
  rw [mem_biunitaryDivisors, Nat.div_self (by omega : 0 < n), gcdUnitary_comm]
  refine ⟨dvd_rfl, hn0, (gcdUnitary_eq_one_iff (by omega) hn0).mpr ?_⟩
  intro e he
  obtain ⟨he1, -⟩ := Finset.mem_inter.mp he
  rw [Nat.mem_unitaryDivisors] at he1
  exact Nat.dvd_one.mp he1.1

private theorem sigmaBiunitary_ge_self {n : ℕ} (hn : 1 ≤ n) : n ≤ sigmaBiunitary n := by
  rw [sigmaBiunitary]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (self_mem_biunitaryDivisors hn)

private theorem sigmaBiunitary_pos {n : ℕ} (hn : 1 ≤ n) : 0 < sigmaBiunitary n :=
  lt_of_lt_of_le (by omega) (sigmaBiunitary_ge_self hn)

private theorem dvd_sigmaBiunitary_of_exact {m n : ℕ} (hcop : m.Coprime n) :
    sigmaBiunitary m ∣ sigmaBiunitary (m * n) := by
  rw [sigmaBiunitary_mul_of_coprime hcop]
  exact dvd_mul_right _ _

private theorem le_of_mod_eq_one {q t : ℕ} (hq : q.Prime) (hmod : q % t = 1) :
    t + 1 ≤ q := by
  rcases lt_or_ge q (t + 1) with hlt | hge
  · rcases lt_or_ge q t with hlt2 | hge2
    · rw [Nat.mod_eq_of_lt hlt2] at hmod
      have hq2 := hq.two_le
      omega
    · have heq : q = t := by omega
      rw [heq, Nat.mod_self] at hmod
      exact (one_ne_zero hmod.symm).elim
  · exact hge

private theorem exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow_aux {p g : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hg : 4 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (p ^ g) ∧ 7 ≤ q := by
  have hu : 3 ≤ g / 2 + 1 := by omega
  obtain ⟨q, hq, hmod⟩ := exists_primitivePrimeDivisor_pow_add_one p (g / 2 + 1)
    hp.two_le (by omega) (fun h => hodd h.1) (fun h => (by omega : g / 2 + 1 ≠ 1) h.1)
  have hdvd1 : q ∣ p ^ (g / 2 + 1) + 1 := by exact_mod_cast hq.dvd
  have hdvd : q ∣ sigmaBiunitary (p ^ g) :=
    hdvd1.trans (pow_add_one_dvd_sum hp g (by omega))
  have hge := le_of_mod_eq_one hq.prime hmod
  exact ⟨q, hq.prime, hdvd, by omega⟩

private theorem exists_prime_gt_five_dvd_sigmaBiunitary_five_pow {g : ℕ} (hg : 2 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (5 ^ g) ∧ 5 < q := by
  have hu : 2 ≤ g / 2 + 1 := by omega
  obtain ⟨q, hq, hmod⟩ := exists_primitivePrimeDivisor_pow_add_one 5 (g / 2 + 1)
    (by decide) (by omega) (fun h => (by decide : (5 : ℕ) ≠ 2) h.1)
    (fun h => (by omega : g / 2 + 1 ≠ 1) h.1)
  have hdvd1 : q ∣ 5 ^ (g / 2 + 1) + 1 := by exact_mod_cast hq.dvd
  have hdvd : q ∣ sigmaBiunitary (5 ^ g) :=
    hdvd1.trans (pow_add_one_dvd_sum (by decide) g (by omega))
  have hge := le_of_mod_eq_one hq.prime hmod
  have hq5 : 5 ≤ q := by omega
  have hqne : q ≠ 5 := by
    intro hqq
    have hmod5 := sigmaBiunitary_prime_pow_mod (by decide : Nat.Prime 5) (by omega : 1 ≤ g)
    rw [hqq] at hdvd
    omega
  exact ⟨q, hq.prime, hdvd, by omega⟩

private theorem sigmaBiunitary_thirteen_cubed : sigmaBiunitary (13 ^ 3) = 2380 := by
  rw [sigmaBiunitary_prime_pow_eq_sum (by decide) (by decide)]
  decide

private theorem exists_prime_dvd_sigmaBiunitary_thirteen_pow {g : ℕ} (hg : 1 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (13 ^ g) ∧ q ∉ ({2, 3, 5, 13} : Finset ℕ) := by
  rcases eq_or_ne g 1 with rfl | h1
  · refine ⟨7, by decide, ?_, by decide⟩
    simp only [pow_one]
    rw [sigmaBiunitary_thirteen]
    decide
  rcases eq_or_ne g 2 with rfl | h2
  · refine ⟨17, by decide, ?_, by decide⟩
    have h169 : (13 : ℕ) ^ 2 = 169 := by decide
    rw [h169, sigmaBiunitary_oneSixtyNine]
    decide
  rcases eq_or_ne g 3 with rfl | h3
  · refine ⟨7, by decide, ?_, by decide⟩
    rw [sigmaBiunitary_thirteen_cubed]
    decide
  · have hg4 : 4 ≤ g := by omega
    obtain ⟨q, hqprime, hdvd, hq7⟩ :=
      exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow_aux (p := 13) (by decide)
        (by decide) hg4
    have hq13 : q ≠ 13 := by
      intro hqq
      have hmod13 := sigmaBiunitary_prime_pow_mod (by decide : Nat.Prime 13)
        (by omega : 1 ≤ g)
      rw [hqq] at hdvd
      omega
    refine ⟨q, hqprime, hdvd, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨by omega, by omega, by omega, hq13⟩

private theorem exists_eq_prime_pow_mul {N p : ℕ} (hN : 0 < N) (hp : p.Prime) :
    ∃ m : ℕ, N = p ^ N.factorization p * m ∧ ¬ p ∣ m ∧ m ≠ 0 := by
  set e := N.factorization p with he
  have hpow : p ^ e ∣ N := (hp.pow_dvd_iff_le_factorization hN.ne').mpr (by omega)
  have hNeq : N = p ^ e * (N / p ^ e) := by
    conv_lhs => rw [← Nat.div_mul_cancel hpow]
    exact mul_comm _ _
  refine ⟨_, hNeq, ?_, ?_⟩
  · intro hpm
    obtain ⟨k, hk⟩ := hpm
    have hsucc : p ^ (e + 1) ∣ N := by
      refine ⟨k, ?_⟩
      rw [hNeq, hk, pow_succ]
      exact (mul_assoc _ _ _).symm
    have hle := (hp.pow_dvd_iff_le_factorization hN.ne').mp hsucc
    omega
  · intro hm0
    rw [hNeq, hm0, mul_zero] at hN
    omega

private theorem aux_e0 {N : ℕ} (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (hf : 3 ≤ N.factorization 3) (he : N.factorization 2 = 0) : False := by
  have h3pow : (3 : ℕ) ^ 3 ∣ N :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mpr hf
  have h27 : (3 : ℕ) ^ 3 = 27 := rfl
  rw [h27] at h3pow
  have hN1 : 1 < N := by
    obtain ⟨k, hk⟩ := h3pow
    omega
  have hoddN : Odd N := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2N
    have h21 : (2 : ℕ) ^ 1 ∣ N := by
      rw [pow_one]
      exact h2N
    have h1 := (Nat.prime_two.pow_dvd_iff_le_factorization hN.ne').mp h21
    omega
  have heven : Even (sigmaBiunitary N) := even_sigmaBiunitary_of_odd_pos hoddN hN1
  rw [hσ, even_iff_two_dvd] at heven
  have h2N : 2 ∣ N := (by decide : Nat.Coprime 2 3).dvd_of_dvd_mul_left heven
  exact hoddN.not_two_dvd_nat h2N

private theorem aux_e1 {N : ℕ} (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (hf : 3 ≤ N.factorization 3) (he : N.factorization 2 = 1) : False := by
  obtain ⟨M, hNM, h2M, hM0⟩ := exists_eq_prime_pow_mul hN Nat.prime_two
  rw [he, pow_one] at hNM
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
  have hcop2M : Nat.Coprime 2 M := Nat.prime_two.coprime_iff_not_dvd.mpr h2M
  have hσN : sigmaBiunitary N = 3 * sigmaBiunitary M := by
    rw [hNM, sigmaBiunitary_mul_of_coprime hcop2M, sigmaBiunitary_two]
  have hσM : sigmaBiunitary M = 2 * M := by
    rw [hσN, hNM] at hσ
    omega
  obtain ⟨m, hMm, h3m, hm0⟩ := exists_eq_prime_pow_mul hMpos Nat.prime_three
  have h3M : 3 ∣ M := by
    have h3pow : (3 : ℕ) ^ 3 ∣ N :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mpr hf
    have h27 : (3 : ℕ) ^ 3 = 27 := rfl
    rw [h27, hNM] at h3pow
    exact (by decide : Nat.Coprime 3 2).dvd_of_dvd_mul_left
      ((by decide : (3 : ℕ) ∣ 27).trans h3pow)
  have hf'M : 1 ≤ M.factorization 3 := by
    have h31 : (3 : ℕ) ^ 1 ∣ M := by
      rw [pow_one]
      exact h3M
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hM0).mp h31
  have hcop3m : Nat.Coprime (3 ^ M.factorization 3) m :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3m).pow_left _
  have hσM2 : sigmaBiunitary M =
      sigmaBiunitary (3 ^ M.factorization 3) * sigmaBiunitary m := by
    conv_lhs => rw [hMm]
    exact sigmaBiunitary_mul_of_coprime hcop3m
  have hσ3pos : 0 < sigmaBiunitary (3 ^ M.factorization 3) := by
    apply sigmaBiunitary_pos
    have hpos : 0 < (3 : ℕ) ^ M.factorization 3 := pow_pos (by decide) _
    omega
  have hσmpos : 0 < sigmaBiunitary m := sigmaBiunitary_pos (Nat.pos_of_ne_zero hm0)
  have hv2 : (sigmaBiunitary (3 ^ M.factorization 3)).factorization 2 +
      (sigmaBiunitary m).factorization 2 = 1 := by
    have hfac := congrArg (fun F : ℕ →₀ ℕ => F 2)
      (Nat.factorization_mul hσ3pos.ne' hσmpos.ne')
    simp only [Finsupp.add_apply] at hfac
    rw [← hσM2, hσM] at hfac
    have h2Mfac : (2 * M).factorization 2 = 1 := by
      have hfac2 := congrArg (fun F : ℕ →₀ ℕ => F 2)
        (Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hM0)
      simp only [Finsupp.add_apply] at hfac2
      have h2fac : (2 : ℕ).factorization 2 = 1 := by
        have h := Nat.prime_two.factorization_pow (k := 1)
        have h1 : ((2 : ℕ) ^ 1).factorization 2 = 1 := by
          rw [h]
          simp
        rw [pow_one] at h1
        exact h1
      have hMfac : M.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2M
      rw [h2fac, hMfac, add_zero] at hfac2
      exact hfac2
    rw [h2Mfac] at hfac
    exact hfac.symm
  have h3odd : Odd (3 ^ M.factorization 3) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    have h23 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    exact (by decide : ¬ (2 : ℕ) ∣ 3) h23
  have h3gt1 : 1 < 3 ^ M.factorization 3 :=
    Nat.one_lt_pow (by omega : M.factorization 3 ≠ 0) (by decide : (1 : ℕ) < 3)
  have heven3 : Even (sigmaBiunitary (3 ^ M.factorization 3)) :=
    even_sigmaBiunitary_of_odd_pos h3odd h3gt1
  have hv3ge1 : 1 ≤ (sigmaBiunitary (3 ^ M.factorization 3)).factorization 2 := by
    have h2dvd : (2 : ℕ) ∣ sigmaBiunitary (3 ^ M.factorization 3) :=
      even_iff_two_dvd.mp heven3
    have h21 : (2 : ℕ) ^ 1 ∣ sigmaBiunitary (3 ^ M.factorization 3) := by
      rw [pow_one]
      exact h2dvd
    exact (Nat.prime_two.pow_dvd_iff_le_factorization hσ3pos.ne').mp h21
  have hvm0 : (sigmaBiunitary m).factorization 2 = 0 := by omega
  have hmodd : Odd (sigmaBiunitary m) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2dvd
    have h21 : (2 : ℕ) ^ 1 ∣ sigmaBiunitary m := by
      rw [pow_one]
      exact h2dvd
    have h1 := (Nat.prime_two.pow_dvd_iff_le_factorization hσmpos.ne').mp h21
    omega
  rw [odd_sigmaBiunitary_iff m (Nat.pos_of_ne_zero hm0)] at hmodd
  obtain ⟨k, hmk⟩ := hmodd
  have hmM : m ∣ M := ⟨3 ^ M.factorization 3, hMm.trans (mul_comm _ _)⟩
  have h2m : ¬ 2 ∣ m := fun h => h2M (h.trans hmM)
  have hm1 : m = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using hmk
    · exfalso
      have h2m' : 2 ∣ m := by
        rw [hmk]
        exact dvd_pow_self 2 (by omega : k ≠ 0)
      exact h2m h2m'
  have hM3 : M = 3 ^ M.factorization 3 := by
    conv_lhs => rw [hMm]
    rw [hm1, mul_one]
  have hσ3eq : sigmaBiunitary (3 ^ M.factorization 3) = 2 * 3 ^ M.factorization 3 := by
    rw [← hM3]
    exact hσM
  have hmod3 := sigmaBiunitary_prime_pow_mod Nat.prime_three hf'M
  rw [hσ3eq] at hmod3
  have h3dvd : (3 : ℕ) ∣ 2 * 3 ^ M.factorization 3 :=
    dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega : M.factorization 3 ≠ 0)) 2
  omega

private theorem aux_e2 {N : ℕ} (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (hf : 3 ≤ N.factorization 3) (he : N.factorization 2 = 2) : False := by
  obtain ⟨M, hNM, h2M, hM0⟩ := exists_eq_prime_pow_mul hN Nat.prime_two
  rw [he] at hNM
  have h4 : (2 : ℕ) ^ 2 = 4 := rfl
  rw [h4] at hNM
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
  have hcop4M : Nat.Coprime 4 M := by
    have hbase : Nat.Coprime 2 M := Nat.prime_two.coprime_iff_not_dvd.mpr h2M
    have h4eq : (4 : ℕ) = 2 ^ 2 := rfl
    rw [h4eq]
    exact hbase.pow_left 2
  have hσN : sigmaBiunitary N = 5 * sigmaBiunitary M := by
    conv_lhs => rw [hNM]
    rw [sigmaBiunitary_mul_of_coprime hcop4M, sigmaBiunitary_four]
  have h5M : 5 ∣ M := by
    have heq : 5 * sigmaBiunitary M = 3 * N := by rw [← hσN, hσ]
    have h5N : (5 : ℕ) ∣ 3 * N := ⟨sigmaBiunitary M, heq.symm⟩
    have h5N' : (5 : ℕ) ∣ N := (by decide : Nat.Coprime 5 3).dvd_of_dvd_mul_left h5N
    rw [hNM] at h5N'
    exact (by decide : Nat.Coprime 5 4).dvd_of_dvd_mul_left h5N'
  obtain ⟨m, hMm, h3m, hm0⟩ := exists_eq_prime_pow_mul hMpos Nat.prime_three
  have h3M : 3 ∣ M := by
    have h3pow : (3 : ℕ) ^ 3 ∣ N :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mpr hf
    have h27 : (3 : ℕ) ^ 3 = 27 := rfl
    rw [h27, hNM] at h3pow
    exact (by decide : Nat.Coprime 3 4).dvd_of_dvd_mul_left
      ((by decide : (3 : ℕ) ∣ 27).trans h3pow)
  have hf'M : 1 ≤ M.factorization 3 := by
    have h31 : (3 : ℕ) ^ 1 ∣ M := by
      rw [pow_one]
      exact h3M
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hM0).mp h31
  have h5m : 5 ∣ m := by
    have h5Mm : (5 : ℕ) ∣ 3 ^ M.factorization 3 * m := by
      rw [← hMm]
      exact h5M
    have h53 : ¬ (5 : ℕ) ∣ 3 ^ M.factorization 3 := by
      intro h
      have h35 : (5 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow (by decide) h
      exact (by decide : ¬ (5 : ℕ) ∣ 3) h35
    rcases (Nat.prime_five.dvd_mul).mp h5Mm with h | h
    · exact absurd h h53
    · exact h
  have hm1 : 1 < m := by
    by_contra h
    have hle : m ≤ 1 := by omega
    have hm01 : m = 1 := by
      have hmpos := Nat.pos_of_ne_zero hm0
      omega
    rw [hm01] at h5m
    exact (by decide : ¬ (5 : ℕ) ∣ 1) h5m
  obtain ⟨R, hmR, h5R, hR0⟩ :=
    exists_eq_prime_pow_mul (Nat.pos_of_ne_zero hm0) Nat.prime_five
  have hg : 1 ≤ m.factorization 5 := by
    have h51 : (5 : ℕ) ^ 1 ∣ m := by
      rw [pow_one]
      exact h5m
    exact (Nat.prime_five.pow_dvd_iff_le_factorization hm0).mp h51
  have hmM : m ∣ M := ⟨3 ^ M.factorization 3, hMm.trans (mul_comm _ _)⟩
  have hRM : R ∣ m := ⟨5 ^ m.factorization 5, hmR.trans (mul_comm _ _)⟩
  have h2R : ¬ 2 ∣ R := fun h => h2M ((h.trans hRM).trans hmM)
  have h3R : ¬ 3 ∣ R := fun h => h3m (h.trans hRM)
  have hR1 : R = 1 := by
    by_contra hRne
    have hRgt1 : 1 < R := by
      have hRpos := Nat.pos_of_ne_zero hR0
      omega
    have hσM : sigmaBiunitary M =
        sigmaBiunitary (3 ^ M.factorization 3) * sigmaBiunitary m := by
      conv_lhs => rw [hMm]
      exact sigmaBiunitary_mul_of_coprime
        (((Nat.prime_three.coprime_iff_not_dvd).mpr h3m).pow_left _)
    have hσm : sigmaBiunitary m =
        sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R := by
      conv_lhs => rw [hmR]
      exact sigmaBiunitary_mul_of_coprime
        (((Nat.prime_five.coprime_iff_not_dvd).mpr h5R).pow_left _)
    have he3 : Even (sigmaBiunitary (3 ^ M.factorization 3)) := by
      apply even_sigmaBiunitary_of_odd_pos
      · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        have h23 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        exact (by decide : ¬ (2 : ℕ) ∣ 3) h23
      · exact Nat.one_lt_pow (by omega : M.factorization 3 ≠ 0) (by decide)
    have he5 : Even (sigmaBiunitary (5 ^ m.factorization 5)) := by
      apply even_sigmaBiunitary_of_odd_pos
      · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        have h25 : (2 : ℕ) ∣ 5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        exact (by decide : ¬ (2 : ℕ) ∣ 5) h25
      · exact Nat.one_lt_pow (by omega : m.factorization 5 ≠ 0) (by decide)
    have heR : Even (sigmaBiunitary R) := by
      apply even_sigmaBiunitary_of_odd_pos _ hRgt1
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact h2R
    have hdvd8 : 8 ∣ sigmaBiunitary N := by
      have e3 : (2 : ℕ) ∣ sigmaBiunitary (3 ^ M.factorization 3) :=
        even_iff_two_dvd.mp he3
      have e5 : (2 : ℕ) ∣ sigmaBiunitary (5 ^ m.factorization 5) :=
        even_iff_two_dvd.mp he5
      have eR : (2 : ℕ) ∣ sigmaBiunitary R := even_iff_two_dvd.mp heR
      have h8 : (8 : ℕ) ∣ sigmaBiunitary (3 ^ M.factorization 3) *
          (sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R) := by
        have h8eq : (8 : ℕ) = 2 * 2 * 2 := rfl
        rw [h8eq, mul_assoc]
        exact mul_dvd_mul e3 (mul_dvd_mul e5 eR)
      have hσN' : sigmaBiunitary N = sigmaBiunitary 4 *
          (sigmaBiunitary (3 ^ M.factorization 3) *
            (sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R)) := by
        conv_lhs => rw [hNM]
        rw [sigmaBiunitary_mul_of_coprime hcop4M, hσM, hσm]
      rw [hσN']
      exact dvd_mul_of_dvd_right h8 _
    rw [hσ] at hdvd8
    rw [hNM] at hdvd8
    have h2M' : 2 ∣ M := by omega
    exact h2M h2M'
  have hf'3 : 3 ≤ M.factorization 3 := by
    have h3pow : (3 : ℕ) ^ 3 ∣ N :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mpr hf
    have h27 : (3 : ℕ) ^ 3 = 27 := rfl
    rw [h27, hNM] at h3pow
    have h27M : (27 : ℕ) ∣ M := (by decide : Nat.Coprime 27 4).dvd_of_dvd_mul_left h3pow
    have h33M : (3 : ℕ) ^ 3 ∣ M := by
      have h273 : (27 : ℕ) = 3 ^ 3 := rfl
      rw [h273] at h27M
      exact h27M
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hM0).mp h33M
  have hNK : N = 3 ^ M.factorization 3 * (4 * 5 ^ m.factorization 5) := by
    conv_lhs => rw [hNM]
    conv_lhs => rw [hMm]
    conv_lhs => rw [hmR]
    rw [hR1, mul_one]
    ring
  have hcop3K : Nat.Coprime (3 ^ M.factorization 3) (4 * 5 ^ m.factorization 5) := by
    have hbase : Nat.Coprime 3 (4 * 5 ^ m.factorization 5) := by
      rw [Nat.prime_three.coprime_iff_not_dvd]
      intro h3
      rcases (Nat.prime_three.dvd_mul).mp h3 with h | h
      · exact (by decide : ¬ (3 : ℕ) ∣ 4) h
      · have h35 : (3 : ℕ) ∣ 5 := Nat.Prime.dvd_of_dvd_pow (by decide) h
        exact (by decide : ¬ (3 : ℕ) ∣ 5) h35
    exact hbase.pow_left _
  have hσ3dvd : sigmaBiunitary (3 ^ M.factorization 3) ∣ 3 * N := by
    have h := dvd_sigmaBiunitary_of_exact hcop3K
    rw [← hNK, hσ] at h
    exact h
  have hn3σ3 : ¬ (3 : ℕ) ∣ sigmaBiunitary (3 ^ M.factorization 3) := by
    intro h
    have hmod := sigmaBiunitary_prime_pow_mod Nat.prime_three hf'M
    omega
  have hcopσ3 : Nat.Coprime (sigmaBiunitary (3 ^ M.factorization 3)) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hn3σ3).symm
  have hσ3dvd2 : sigmaBiunitary (3 ^ M.factorization 3) ∣ 4 * 5 ^ m.factorization 5 := by
    have h1 : sigmaBiunitary (3 ^ M.factorization 3) ∣ N :=
      hcopσ3.dvd_of_dvd_mul_left hσ3dvd
    rw [hNK] at h1
    have hcopσ3pow :
        Nat.Coprime (sigmaBiunitary (3 ^ M.factorization 3)) (3 ^ M.factorization 3) :=
      hcopσ3.pow_right _
    exact hcopσ3pow.dvd_of_dvd_mul_left h1
  have hf'eq3 : M.factorization 3 = 3 := by
    by_contra hne
    have hf4 : 4 ≤ M.factorization 3 := by omega
    obtain ⟨q, hqprime, hqdvd, hq7⟩ :=
      exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow_aux Nat.prime_three
        (by decide) hf4
    have hqdvd2 : q ∣ 4 * 5 ^ m.factorization 5 := hqdvd.trans hσ3dvd2
    rcases (hqprime.dvd_mul).mp hqdvd2 with h | h
    · have hq2 : q ∣ 2 := by
        have h4 : (4 : ℕ) = 2 ^ 2 := rfl
        rw [h4] at h
        exact Nat.Prime.dvd_of_dvd_pow hqprime h
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hq2
      have hq2' := hqprime.two_le
      omega
    · have hq5 : q ∣ 5 := Nat.Prime.dvd_of_dvd_pow hqprime h
      have hle := Nat.le_of_dvd (by decide : 0 < 5) hq5
      omega
  have hN108 : N = 108 * 5 ^ m.factorization 5 := by
    conv_lhs => rw [hNM]
    conv_lhs => rw [hMm]
    rw [hf'eq3]
    conv_lhs => rw [hmR]
    rw [hR1, mul_one]
    have h323 : (3 : ℕ) ^ 3 = 27 := rfl
    rw [h323]
    ring
  have hσ108 : sigmaBiunitary 108 = 200 := by
    have h108 : (108 : ℕ) = 4 * 27 := rfl
    rw [h108, sigmaBiunitary_mul_of_coprime
      (by decide : Nat.Coprime 4 27), sigmaBiunitary_four, sigmaBiunitary_twentySeven]
  have h200dvd : (200 : ℕ) ∣ 3 * N := by
    have hcop108 : Nat.Coprime 108 (5 ^ m.factorization 5) :=
      (((by decide : Nat.Coprime 5 108).pow_left _).symm)
    have h := dvd_sigmaBiunitary_of_exact hcop108
    rw [← hN108, hσ108, hσ] at h
    exact h
  have hg2 : 2 ≤ m.factorization 5 := by
    have h25 : (25 : ℕ) ∣ 3 * N := (by decide : (25 : ℕ) ∣ 200).trans h200dvd
    rw [hN108] at h25
    have h25a : (25 : ℕ) ∣ 108 * 5 ^ m.factorization 5 :=
      (by decide : Nat.Coprime 25 3).dvd_of_dvd_mul_left h25
    have h25b : (25 : ℕ) ∣ 5 ^ m.factorization 5 :=
      (by decide : Nat.Coprime 25 108).dvd_of_dvd_mul_left h25a
    have h52 : (5 : ℕ) ^ 2 ∣ 5 ^ m.factorization 5 := by
      have h252 : (25 : ℕ) = 5 ^ 2 := rfl
      rw [h252] at h25b
      exact h25b
    have hle := (Nat.prime_five.pow_dvd_iff_le_factorization
      (pow_ne_zero _ (by decide))).mp h52
    have hfac5 : (5 ^ m.factorization 5).factorization 5 = m.factorization 5 := by
      rw [Nat.prime_five.factorization_pow]
      simp
    rw [hfac5] at hle
    exact hle
  obtain ⟨q, hqprime, hqdvd, hqgt5⟩ :=
    exists_prime_gt_five_dvd_sigmaBiunitary_five_pow hg2
  have hσ5dvd : sigmaBiunitary (5 ^ m.factorization 5) ∣ 3 * N := by
    have hN5 : N = 5 ^ m.factorization 5 * 108 := by
      rw [hN108, mul_comm]
    have hcop5 : Nat.Coprime (5 ^ m.factorization 5) 108 :=
      (by decide : Nat.Coprime 5 108).pow_left _
    have h := dvd_sigmaBiunitary_of_exact hcop5
    rw [← hN5, hσ] at h
    exact h
  have hq3N : q ∣ 3 * N := hqdvd.trans hσ5dvd
  rw [hN108] at hq3N
  rcases (hqprime.dvd_mul).mp hq3N with h | h
  · have hle := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  · rcases (hqprime.dvd_mul).mp h with h | h
    · have h108eq : (108 : ℕ) = 4 * 27 := rfl
      rw [h108eq] at h
      rcases (hqprime.dvd_mul).mp h with h | h
      · have hq2 : q ∣ 2 := by
          have h4 : (4 : ℕ) = 2 ^ 2 := rfl
          rw [h4] at h
          exact Nat.Prime.dvd_of_dvd_pow hqprime h
        have hle := Nat.le_of_dvd (by decide : 0 < 2) hq2
        omega
      · have hq3 : q ∣ 3 := by
          have h27 : (27 : ℕ) = 3 ^ 3 := rfl
          rw [h27] at h
          exact Nat.Prime.dvd_of_dvd_pow hqprime h
        have hle := Nat.le_of_dvd (by decide : 0 < 3) hq3
        omega
    · have hq5 : q ∣ 5 := Nat.Prime.dvd_of_dvd_pow hqprime h
      have hle := Nat.le_of_dvd (by decide : 0 < 5) hq5
      omega

private theorem aux_e3 {N : ℕ} (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (hf : 3 ≤ N.factorization 3) (he : N.factorization 2 = 3) : False := by
  obtain ⟨M, hNM, h2M, hM0⟩ := exists_eq_prime_pow_mul hN Nat.prime_two
  rw [he] at hNM
  have h8 : (2 : ℕ) ^ 3 = 8 := rfl
  rw [h8] at hNM
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
  have hcop8M : Nat.Coprime 8 M := by
    have hbase : Nat.Coprime 2 M := Nat.prime_two.coprime_iff_not_dvd.mpr h2M
    have h8eq : (8 : ℕ) = 2 ^ 3 := rfl
    rw [h8eq]
    exact hbase.pow_left 3
  have hσN : sigmaBiunitary N = 15 * sigmaBiunitary M := by
    conv_lhs => rw [hNM]
    rw [sigmaBiunitary_mul_of_coprime hcop8M, sigmaBiunitary_eight]
  have h5M : 5 ∣ M := by
    have heq : 15 * sigmaBiunitary M = 3 * N := by rw [← hσN, hσ]
    have h5N : (5 : ℕ) ∣ 3 * N := ⟨3 * sigmaBiunitary M, by omega⟩
    have h5N' : (5 : ℕ) ∣ N := (by decide : Nat.Coprime 5 3).dvd_of_dvd_mul_left h5N
    rw [hNM] at h5N'
    exact (by decide : Nat.Coprime 5 8).dvd_of_dvd_mul_left h5N'
  obtain ⟨m, hMm, h3m, hm0⟩ := exists_eq_prime_pow_mul hMpos Nat.prime_three
  have h3M : 3 ∣ M := by
    have h3pow : (3 : ℕ) ^ 3 ∣ N :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mpr hf
    have h27 : (3 : ℕ) ^ 3 = 27 := rfl
    rw [h27, hNM] at h3pow
    exact (by decide : Nat.Coprime 3 8).dvd_of_dvd_mul_left
      ((by decide : (3 : ℕ) ∣ 27).trans h3pow)
  have hf'M : 1 ≤ M.factorization 3 := by
    have h31 : (3 : ℕ) ^ 1 ∣ M := by
      rw [pow_one]
      exact h3M
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hM0).mp h31
  have hf'3 : 3 ≤ M.factorization 3 := by
    have h3pow : (3 : ℕ) ^ 3 ∣ N :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mpr hf
    have h27 : (3 : ℕ) ^ 3 = 27 := rfl
    rw [h27, hNM] at h3pow
    have h27M : (27 : ℕ) ∣ M := (by decide : Nat.Coprime 27 8).dvd_of_dvd_mul_left h3pow
    have h33M : (3 : ℕ) ^ 3 ∣ M := by
      have h273 : (27 : ℕ) = 3 ^ 3 := rfl
      rw [h273] at h27M
      exact h27M
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hM0).mp h33M
  have h5m : 5 ∣ m := by
    have h5Mm : (5 : ℕ) ∣ 3 ^ M.factorization 3 * m := by
      rw [← hMm]
      exact h5M
    have h53 : ¬ (5 : ℕ) ∣ 3 ^ M.factorization 3 := by
      intro h
      have h35 : (5 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow (by decide) h
      exact (by decide : ¬ (5 : ℕ) ∣ 3) h35
    rcases (Nat.prime_five.dvd_mul).mp h5Mm with h | h
    · exact absurd h h53
    · exact h
  obtain ⟨R, hmR, h5R, hR0⟩ :=
    exists_eq_prime_pow_mul (Nat.pos_of_ne_zero hm0) Nat.prime_five
  have hg : 1 ≤ m.factorization 5 := by
    have h51 : (5 : ℕ) ^ 1 ∣ m := by
      rw [pow_one]
      exact h5m
    exact (Nat.prime_five.pow_dvd_iff_le_factorization hm0).mp h51
  have hmM : m ∣ M := ⟨3 ^ M.factorization 3, hMm.trans (mul_comm _ _)⟩
  have hRM : R ∣ m := ⟨5 ^ m.factorization 5, hmR.trans (mul_comm _ _)⟩
  have h2R : ¬ 2 ∣ R := fun h => h2M ((h.trans hRM).trans hmM)
  have h3R : ¬ 3 ∣ R := fun h => h3m (h.trans hRM)
  have hσM : sigmaBiunitary M =
      sigmaBiunitary (3 ^ M.factorization 3) * sigmaBiunitary m := by
    conv_lhs => rw [hMm]
    exact sigmaBiunitary_mul_of_coprime
      (((Nat.prime_three.coprime_iff_not_dvd).mpr h3m).pow_left _)
  have hσm : sigmaBiunitary m =
      sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R := by
    conv_lhs => rw [hmR]
    exact sigmaBiunitary_mul_of_coprime
      (((Nat.prime_five.coprime_iff_not_dvd).mpr h5R).pow_left _)
  have hσN' : sigmaBiunitary N = 15 * (sigmaBiunitary (3 ^ M.factorization 3) *
      (sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R)) := by
    conv_lhs => rw [hNM]
    rw [sigmaBiunitary_mul_of_coprime hcop8M, sigmaBiunitary_eight, hσM, hσm]
  have hNeqFull : N = 8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) := by
    rw [hNM]
    congr 1
    conv_lhs => rw [hMm]
    exact congrArg _ hmR
  have hRge : R ≤ sigmaBiunitary R := sigmaBiunitary_ge_self (Nat.pos_of_ne_zero hR0)
  by_cases hg2 : m.factorization 5 = 2
  · have hσ25 : sigmaBiunitary (5 ^ m.factorization 5) = 26 := by
      rw [hg2]
      have h52 : (5 : ℕ) ^ 2 = 25 := rfl
      rw [h52]
      exact sigmaBiunitary_twentyFive
    have hN5 : N = 5 ^ m.factorization 5 * (8 * (3 ^ M.factorization 3 * R)) := by
      rw [hNeqFull]
      ring
    have hcop5K : Nat.Coprime (5 ^ m.factorization 5) (8 * (3 ^ M.factorization 3 * R)) := by
      have hbase : Nat.Coprime 5 (8 * (3 ^ M.factorization 3 * R)) := by
        rw [Nat.prime_five.coprime_iff_not_dvd]
        intro h5
        rcases (Nat.prime_five.dvd_mul).mp h5 with h | h
        · exact (by decide : ¬ (5 : ℕ) ∣ 8) h
        · rcases (Nat.prime_five.dvd_mul).mp h with h | h
          · have h53 : (5 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow (by decide) h
            exact (by decide : ¬ (5 : ℕ) ∣ 3) h53
          · exact h5R h
      exact hbase.pow_left _
    have hσ5dvd : sigmaBiunitary (5 ^ m.factorization 5) ∣ 3 * N := by
      have h := dvd_sigmaBiunitary_of_exact hcop5K
      rw [← hN5, hσ] at h
      exact h
    rw [hσ25] at hσ5dvd
    have h13N : 13 ∣ N := by
      have h13 : (13 : ℕ) ∣ 3 * N := (by decide : (13 : ℕ) ∣ 26).trans hσ5dvd
      exact (by decide : Nat.Coprime 13 3).dvd_of_dvd_mul_left h13
    have h13R : 13 ∣ R := by
      have h13Neq : (13 : ℕ) ∣ 8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) := by
        rw [← hNeqFull]
        exact h13N
      have h138 : ¬ (13 : ℕ) ∣ 8 := by decide
      have h133 : ¬ (13 : ℕ) ∣ 3 ^ M.factorization 3 := by
        intro h
        have h313 : (13 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow (by decide) h
        exact (by decide : ¬ (13 : ℕ) ∣ 3) h313
      have h135 : ¬ (13 : ℕ) ∣ 5 ^ m.factorization 5 := by
        intro h
        have h515 : (13 : ℕ) ∣ 5 := Nat.Prime.dvd_of_dvd_pow (by decide) h
        exact (by decide : ¬ (13 : ℕ) ∣ 5) h515
      have hp13 : Nat.Prime 13 := by decide
      rcases (hp13.dvd_mul).mp h13Neq with h | h
      · exact absurd h h138
      · rcases (hp13.dvd_mul).mp h with h | h
        · exact absurd h h133
        · rcases (hp13.dvd_mul).mp h with h | h
          · exact absurd h h135
          · exact h
    obtain ⟨R', hRR', h13R', hR'0⟩ :=
      exists_eq_prime_pow_mul (Nat.pos_of_ne_zero hR0) (by decide : Nat.Prime 13)
    have he2 : 1 ≤ R.factorization 13 := by
      have h131 : (13 : ℕ) ^ 1 ∣ R := by
        rw [pow_one]
        exact h13R
      exact ((by decide : Nat.Prime 13).pow_dvd_iff_le_factorization hR0).mp h131
    obtain ⟨p3, hp3prime, hp3dvd, hp3out⟩ :=
      exists_prime_dvd_sigmaBiunitary_thirteen_pow he2
    have hp3ne : p3 ≠ 2 ∧ p3 ≠ 3 ∧ p3 ≠ 5 ∧ p3 ≠ 13 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hp3out
    have hσ13dvd : sigmaBiunitary (13 ^ R.factorization 13) ∣ 3 * N := by
      have hN13 : N = 13 ^ R.factorization 13 *
          (8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R'))) := by
        rw [hNeqFull]
        conv_lhs => rw [hRR']
        ring
      have hcop13 : Nat.Coprime (13 ^ R.factorization 13)
          (8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R'))) := by
        have hbase : Nat.Coprime 13
            (8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R'))) := by
          rw [(by decide : Nat.Prime 13).coprime_iff_not_dvd]
          intro h13
          have h138 : ¬ (13 : ℕ) ∣ 8 := by decide
          have h133 : ¬ (13 : ℕ) ∣ 3 ^ M.factorization 3 := by
            intro h
            have h313 : (13 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow (by decide) h
            exact (by decide : ¬ (13 : ℕ) ∣ 3) h313
          have h135 : ¬ (13 : ℕ) ∣ 5 ^ m.factorization 5 := by
            intro h
            have h515 : (13 : ℕ) ∣ 5 := Nat.Prime.dvd_of_dvd_pow (by decide) h
            exact (by decide : ¬ (13 : ℕ) ∣ 5) h515
          have hp13 : Nat.Prime 13 := by decide
          rcases (hp13.dvd_mul).mp h13 with h | h
          · exact absurd h h138
          · rcases (hp13.dvd_mul).mp h with h | h
            · exact absurd h h133
            · rcases (hp13.dvd_mul).mp h with h | h
              · exact absurd h h135
              · exact absurd h h13R'
        exact hbase.pow_left _
      have h := dvd_sigmaBiunitary_of_exact hcop13
      rw [← hN13, hσ] at h
      exact h
    have hp33N : p3 ∣ 3 * N := hp3dvd.trans hσ13dvd
    have hp3N : p3 ∣ N := by
      have hcop : Nat.Coprime p3 3 := by
        rw [hp3prime.coprime_iff_not_dvd]
        intro hdiv
        have hle := Nat.le_of_dvd (by decide : 0 < 3) hdiv
        have h2le := hp3prime.two_le
        omega
      exact hcop.dvd_of_dvd_mul_left hp33N
    have hp3R' : p3 ∣ R' := by
      have hNeqFull2 : N = 8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 *
          (13 ^ R.factorization 13 * R'))) := by
        rw [hNeqFull]
        exact congrArg
          (fun X => 8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * X))) hRR'
      have hp3Neq : p3 ∣ 8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 *
          (13 ^ R.factorization 13 * R'))) := by
        rw [← hNeqFull2]
        exact hp3N
      have hp3n8 : ¬ p3 ∣ 8 := by
        intro h
        have h8 : (8 : ℕ) = 2 ^ 3 := rfl
        rw [h8] at h
        have h2 : p3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp3prime h
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | heq
        · have h2le := hp3prime.two_le
          omega
        · exact hp3ne.1 heq
      have hp3n3 : ¬ p3 ∣ 3 ^ M.factorization 3 := by
        intro h
        have h3 : p3 ∣ 3 := Nat.Prime.dvd_of_dvd_pow hp3prime h
        rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | heq
        · have h2le := hp3prime.two_le
          omega
        · exact hp3ne.2.1 heq
      have hp3n5 : ¬ p3 ∣ 5 ^ m.factorization 5 := by
        intro h
        have h5 : p3 ∣ 5 := Nat.Prime.dvd_of_dvd_pow hp3prime h
        rcases (Nat.dvd_prime Nat.prime_five).mp h5 with h1 | heq
        · have h2le := hp3prime.two_le
          omega
        · exact hp3ne.2.2.1 heq
      have hp3n13 : ¬ p3 ∣ 13 ^ R.factorization 13 := by
        intro h
        have h13 : p3 ∣ 13 := Nat.Prime.dvd_of_dvd_pow hp3prime h
        rcases (Nat.dvd_prime (by decide : Nat.Prime 13)).mp h13 with h1 | heq
        · have h2le := hp3prime.two_le
          omega
        · exact hp3ne.2.2.2 heq
      rcases (hp3prime.dvd_mul).mp hp3Neq with h | h
      · exact absurd h hp3n8
      · rcases (hp3prime.dvd_mul).mp h with h | h
        · exact absurd h hp3n3
        · rcases (hp3prime.dvd_mul).mp h with h | h
          · exact absurd h hp3n5
          · rcases (hp3prime.dvd_mul).mp h with h | h
            · exact absurd h hp3n13
            · exact h
    obtain ⟨R'', hR'R'', hp3R'', hR''0⟩ :=
      exists_eq_prime_pow_mul (Nat.pos_of_ne_zero hR'0) hp3prime
    have he3 : 1 ≤ R'.factorization p3 := by
      have h1 : p3 ^ 1 ∣ R' := by
        rw [pow_one]
        exact hp3R'
      exact (hp3prime.pow_dvd_iff_le_factorization hR'0).mp h1
    have hσR : sigmaBiunitary R =
        sigmaBiunitary (13 ^ R.factorization 13) * sigmaBiunitary R' := by
      conv_lhs => rw [hRR']
      exact sigmaBiunitary_mul_of_coprime
        ((((by decide : Nat.Prime 13).coprime_iff_not_dvd).mpr h13R').pow_left _)
    have hσR' : sigmaBiunitary R' =
        sigmaBiunitary (p3 ^ R'.factorization p3) * sigmaBiunitary R'' := by
      conv_lhs => rw [hR'R'']
      exact sigmaBiunitary_mul_of_coprime
        (((hp3prime.coprime_iff_not_dvd).mpr hp3R'').pow_left _)
    have he13 : Even (sigmaBiunitary (13 ^ R.factorization 13)) := by
      apply even_sigmaBiunitary_of_odd_pos
      · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        have h213 : (2 : ℕ) ∣ 13 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        exact (by decide : ¬ (2 : ℕ) ∣ 13) h213
      · exact Nat.one_lt_pow (by omega : R.factorization 13 ≠ 0)
          ((by decide : Nat.Prime 13).one_lt)
    have hep3 : Even (sigmaBiunitary (p3 ^ R'.factorization p3)) := by
      apply even_sigmaBiunitary_of_odd_pos
      · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        have h2p3 : (2 : ℕ) ∣ p3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        rcases (Nat.dvd_prime hp3prime).mp h2p3 with h1 | heq
        · exact (by decide : (2 : ℕ) ≠ 1) h1
        · exact hp3ne.1 heq.symm
      · exact Nat.one_lt_pow (by omega : R'.factorization p3 ≠ 0) hp3prime.one_lt
    have he3' : Even (sigmaBiunitary (3 ^ M.factorization 3)) := by
      apply even_sigmaBiunitary_of_odd_pos
      · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        have h23 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        exact (by decide : ¬ (2 : ℕ) ∣ 3) h23
      · exact Nat.one_lt_pow (by omega : M.factorization 3 ≠ 0) (by decide)
    have he5' : Even (sigmaBiunitary (5 ^ m.factorization 5)) := by
      apply even_sigmaBiunitary_of_odd_pos
      · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        have h25 : (2 : ℕ) ∣ 5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        exact (by decide : ¬ (2 : ℕ) ∣ 5) h25
      · exact Nat.one_lt_pow (by omega : m.factorization 5 ≠ 0) (by decide)
    have hσNfull : sigmaBiunitary N = sigmaBiunitary 8 *
        (sigmaBiunitary (3 ^ M.factorization 3) * (sigmaBiunitary (5 ^ m.factorization 5) *
          (sigmaBiunitary (13 ^ R.factorization 13) *
            (sigmaBiunitary (p3 ^ R'.factorization p3) * sigmaBiunitary R'')))) := by
      conv_lhs => rw [hNM]
      rw [sigmaBiunitary_mul_of_coprime hcop8M, hσM, hσm, hσR, hσR']
    have h16N : (16 : ℕ) ∣ sigmaBiunitary N := by
      have e3 : (2 : ℕ) ∣ sigmaBiunitary (3 ^ M.factorization 3) :=
        even_iff_two_dvd.mp he3'
      have e5 : (2 : ℕ) ∣ sigmaBiunitary (5 ^ m.factorization 5) :=
        even_iff_two_dvd.mp he5'
      have e13 : (2 : ℕ) ∣ sigmaBiunitary (13 ^ R.factorization 13) :=
        even_iff_two_dvd.mp he13
      have ep3 : (2 : ℕ) ∣ sigmaBiunitary (p3 ^ R'.factorization p3) :=
        even_iff_two_dvd.mp hep3
      have h16sub : (16 : ℕ) ∣ sigmaBiunitary (3 ^ M.factorization 3) *
          (sigmaBiunitary (5 ^ m.factorization 5) *
            (sigmaBiunitary (13 ^ R.factorization 13) *
              sigmaBiunitary (p3 ^ R'.factorization p3))) := by
        have h4a : (2 : ℕ) * 2 ∣ sigmaBiunitary (3 ^ M.factorization 3) *
            sigmaBiunitary (5 ^ m.factorization 5) := mul_dvd_mul e3 e5
        have h4b : (2 : ℕ) * 2 ∣ sigmaBiunitary (13 ^ R.factorization 13) *
            sigmaBiunitary (p3 ^ R'.factorization p3) := mul_dvd_mul e13 ep3
        have h16 : (2 * 2) * (2 * 2) ∣ (sigmaBiunitary (3 ^ M.factorization 3) *
            sigmaBiunitary (5 ^ m.factorization 5)) *
            (sigmaBiunitary (13 ^ R.factorization 13) *
              sigmaBiunitary (p3 ^ R'.factorization p3)) := mul_dvd_mul h4a h4b
        have e16 : ((2 : ℕ) * 2) * (2 * 2) = 16 := rfl
        have eS : (sigmaBiunitary (3 ^ M.factorization 3) *
            sigmaBiunitary (5 ^ m.factorization 5)) *
            (sigmaBiunitary (13 ^ R.factorization 13) *
              sigmaBiunitary (p3 ^ R'.factorization p3)) =
            sigmaBiunitary (3 ^ M.factorization 3) * (sigmaBiunitary (5 ^ m.factorization 5) *
              (sigmaBiunitary (13 ^ R.factorization 13) *
                sigmaBiunitary (p3 ^ R'.factorization p3))) := by ring
        rw [e16, eS] at h16
        exact h16
      have hform : sigmaBiunitary (3 ^ M.factorization 3) *
          (sigmaBiunitary (5 ^ m.factorization 5) * (sigmaBiunitary (13 ^ R.factorization 13) *
            (sigmaBiunitary (p3 ^ R'.factorization p3) * sigmaBiunitary R''))) =
          (sigmaBiunitary (3 ^ M.factorization 3) * (sigmaBiunitary (5 ^ m.factorization 5) *
            (sigmaBiunitary (13 ^ R.factorization 13) *
              sigmaBiunitary (p3 ^ R'.factorization p3)))) * sigmaBiunitary R'' := by
        ring
      rw [hσNfull, hform]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h16sub _) _
    have h16dvd : (16 : ℕ) ∣ 3 * N := by
      rw [← hσ]
      exact h16N
    have h16N' : (16 : ℕ) ∣ N := (by decide : Nat.Coprime 16 3).dvd_of_dvd_mul_left h16dvd
    have h24 : (2 : ℕ) ^ 4 ∣ N := by
      have h216 : (2 : ℕ) ^ 4 = 16 := rfl
      rw [h216]
      exact h16N'
    have h4le := (Nat.prime_two.pow_dvd_iff_le_factorization hN.ne').mp h24
    omega
  · have h81 : 112 * 3 ^ M.factorization 3 ≤
        81 * sigmaBiunitary (3 ^ M.factorization 3) := by
      have h := (sigmaBiunitary_prime_pow_div_ge 3 (M.factorization 3)
        Nat.prime_three (by omega : 0 < M.factorization 3)).2.2 hf'3
      have h112eq : (1 + 1 / ((3 : ℕ) : ℚ)) * (1 + 1 / ((3 : ℕ) : ℚ) ^ 3) = 112 / 81 := by
        norm_num
      rw [h112eq] at h
      have hpos81 : (0 : ℚ) < 81 := by norm_num
      have hpos3 : (0 : ℚ) < ((3 : ℕ) : ℚ) ^ M.factorization 3 := by positivity
      rw [div_le_div_iff₀ hpos81 hpos3] at h
      have h' : (112 : ℚ) * (3 : ℚ) ^ M.factorization 3 ≤
          81 * (sigmaBiunitary (3 ^ M.factorization 3) : ℚ) := by
        rw [mul_comm _ (81 : ℚ)] at h
        exact h
      exact_mod_cast h'
    have h6 : 6 * 5 ^ m.factorization 5 ≤
        5 * sigmaBiunitary (5 ^ m.factorization 5) := by
      have h := (sigmaBiunitary_prime_pow_div_ge 5 (m.factorization 5)
        Nat.prime_five (by omega : 0 < m.factorization 5)).2.1 hg2
      have h65eq : (1 : ℚ) + 1 / ((5 : ℕ) : ℚ) = 6 / 5 := by norm_num
      rw [h65eq] at h
      have hpos5 : (0 : ℚ) < 5 := by norm_num
      have hpos5p : (0 : ℚ) < ((5 : ℕ) : ℚ) ^ m.factorization 5 := by positivity
      rw [div_le_div_iff₀ hpos5 hpos5p] at h
      have h' : (6 : ℚ) * (5 : ℚ) ^ m.factorization 5 ≤
          5 * (sigmaBiunitary (5 ^ m.factorization 5) : ℚ) := by
        rw [mul_comm _ (5 : ℚ)] at h
        exact h
      exact_mod_cast h'
    have step1 : (112 * 3 ^ M.factorization 3) * (6 * 5 ^ m.factorization 5) * R ≤
        (81 * sigmaBiunitary (3 ^ M.factorization 3)) *
          (5 * sigmaBiunitary (5 ^ m.factorization 5)) * sigmaBiunitary R := by
      apply mul_le_mul _ hRge (by positivity) (by positivity)
      apply mul_le_mul h81 h6 (by positivity) (by positivity)
    have hfin : 405 * (24 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R))) <
        405 * (15 * (sigmaBiunitary (3 ^ M.factorization 3) *
          (sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R))) := by
      have hpos : 0 < 3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R) := by
        positivity
      have h10080 : (9720 : ℕ) * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) <
          10080 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) := by
        have h360 : 0 < 360 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) := by
          positivity
        omega
      calc 405 * (24 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)))
          = 9720 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) := by ring
        _ < 10080 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) := h10080
        _ = 15 * ((112 * 3 ^ M.factorization 3) * (6 * 5 ^ m.factorization 5) * R) := by
            ring
        _ ≤ 15 * ((81 * sigmaBiunitary (3 ^ M.factorization 3)) *
            (5 * sigmaBiunitary (5 ^ m.factorization 5)) * sigmaBiunitary R) :=
            Nat.mul_le_mul_left 15 step1
        _ = 405 * (15 * (sigmaBiunitary (3 ^ M.factorization 3) *
            (sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R))) := by ring
    have hcancel : 24 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) <
        15 * (sigmaBiunitary (3 ^ M.factorization 3) *
          (sigmaBiunitary (5 ^ m.factorization 5) * sigmaBiunitary R)) :=
      lt_of_mul_lt_mul_left hfin (by decide)
    have hcontra : 3 * N < sigmaBiunitary N := by
      rw [hσN', hNeqFull]
      have heq : 3 * (8 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R))) =
          24 * (3 ^ M.factorization 3 * (5 ^ m.factorization 5 * R)) := by ring
      rw [heq]
      exact hcancel
    rw [hσ] at hcontra
    omega

/-- **Biunitary triperfect numbers divisible by $27$ are divisible by $16$.** Let $N$ be a
biunitary triperfect number, that is, a positive integer with $\sigma^{**}(N) = 3N$, where
$\sigma^{**}$ is the biunitary divisor sum. If $3^3$ divides $N$, then $2^4$ divides $N$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 9 (`jis-2025-25.4.5-lem-9`). -/
public theorem four_le_factorization_two_of_biunitaryTriperfect (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    4 ≤ N.factorization 2 := by
  by_contra h
  have hle : N.factorization 2 ≤ 3 := by omega
  rcases (by omega : N.factorization 2 = 0 ∨ N.factorization 2 = 1 ∨
    N.factorization 2 = 2 ∨ N.factorization 2 = 3) with h0 | h1 | h2 | h3
  · exact aux_e0 hN hσ hf h0
  · exact aux_e1 hN hσ hf h1
  · exact aux_e2 hN hσ hf h2
  · exact aux_e3 hN hσ hf h3


-- Lemma 3 at `p = 5`: for `g ≥ 3`, `σ**(5 ^ g) / 5 ^ g ≥ (1 + 1/5)(1 + 1/125) > 6/5`.
private theorem five_mul_sigmaBiunitary_five_pow_gt {g : ℕ} (hg : 3 ≤ g) :
    6 * 5 ^ g < 5 * sigmaBiunitary (5 ^ g) := by
  have hb := (sigmaBiunitary_prime_pow_div_ge 5 g (by decide) (by omega)).2.2 hg
  have hpos : (0 : ℚ) < (5 : ℚ) ^ g := by positivity
  push_cast at hb
  rw [le_div_iff₀ hpos] at hb
  have hlt : (6 : ℚ) * 5 ^ g < 5 * sigmaBiunitary (5 ^ g) := by linarith
  exact_mod_cast hlt

-- An odd `m` with `σ**(m) / m = 6/5` is `5`.
private theorem eq_five_of_sigmaBiunitary_ratio {m : ℕ} (hm : Odd m)
    (hs : 5 * sigmaBiunitary m = 6 * m) : m = 5 := by
  have hm0 : m ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hm)
  have h5 : 5 ∣ m := (by decide : Nat.Coprime 5 6).dvd_of_dvd_mul_left
    (hs ▸ Nat.dvd_mul_right 5 (sigmaBiunitary m))
  let g := m.factorization 5
  let r := ordCompl[5] m
  have hg : 0 < g := (by decide : Nat.Prime 5).factorization_pos_of_dvd hm0 h5
  have hr0 : r ≠ 0 := (Nat.ordCompl_pos 5 hm0).ne'
  have hmr : 5 ^ g * r = m := Nat.ordProj_mul_ordCompl_eq_self m 5
  have hpr : (5 ^ g).Coprime r :=
    (Nat.coprime_ordCompl (by decide : Nat.Prime 5) hm0).pow_left g
  have hmul := sigmaBiunitary_mul_of_coprime hpr
  have hro : Odd r := Nat.Odd.of_mul_right (hmr ▸ hm)
  have hpo : Odd ((5 : ℕ) ^ g) := (by decide : Odd (5 : ℕ)).pow
  have hpe : Even (sigmaBiunitary (5 ^ g)) :=
    even_sigmaBiunitary_of_odd_pos hpo (Nat.one_lt_pow hg.ne' (by decide : 1 < (5 : ℕ)))
  have hr1 : r = 1 := by
    by_contra hr1
    have hre : Even (sigmaBiunitary r) := even_sigmaBiunitary_of_odd_pos hro
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hr0, hr1⟩)
    obtain ⟨a, ha⟩ := hpe
    obtain ⟨b, hb⟩ := hre
    have hmul' : sigmaBiunitary m = sigmaBiunitary (5 ^ g) * sigmaBiunitary r := by
      simpa only [hmr] using hmul
    have hme : Even (3 * m) := ⟨5 * a * b, by nlinarith [hmul']⟩
    exact (Nat.not_odd_iff_even.mpr
      ((Nat.even_mul.mp hme).resolve_left (by decide : ¬ Even (3 : ℕ)))) hm
  have hmp : m = 5 ^ g := by simpa only [hr1, mul_one] using hmr.symm
  have hsg : 5 * sigmaBiunitary (5 ^ g) = 6 * 5 ^ g := by simpa only [hmp] using hs
  have hgle : g ≤ 2 := by
    by_contra h
    have := five_mul_sigmaBiunitary_five_pow_gt (by omega : 3 ≤ g)
    omega
  have hg2 : g ≠ 2 := by
    intro h
    have h25 : 5 * sigmaBiunitary 25 = 6 * 25 := by
      simpa only [h, show (5 : ℕ) ^ 2 = 25 by decide] using hsg
    rw [sigmaBiunitary_twentyFive] at h25
    omega
  have hg1 : g = 1 := by omega
  simpa only [hg1, pow_one] using hmp

/-- **Biunitary triperfect numbers exactly divisible by $2^4$ and by $3^3$ or $3^4$.** Let $N$ be
a biunitary triperfect number, that is, a positive integer with $\sigma^{**}(N) = 3N$, where
$\sigma^{**}$ is the biunitary divisor sum. If the exact power of $2$ dividing $N$ is $2^4$ and the
exact power of $3$ dividing $N$ is $3^3$ or $3^4$, then $N = 2160$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 14 (`jis-2025-25.4.5-lem-14`). -/
public theorem eq_2160_of_factorization_two_eq_four (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3)
    (he : N.factorization 2 = 4) (hf4 : N.factorization 3 ≤ 4) : N = 2160 := by
  let a := ordCompl[2] N
  have ha0 : a ≠ 0 := (Nat.ordCompl_pos 2 hN.ne').ne'
  have hna : 16 * a = N := by
    simpa only [a, he, show (2 : ℕ) ^ 4 = 16 by decide] using
      Nat.ordProj_mul_ordCompl_eq_self N 2
  have ha2 : Nat.Coprime 16 a := by
    simpa only [show (2 : ℕ) ^ 4 = 16 by decide] using
      (Nat.coprime_ordCompl Nat.prime_two hN.ne').pow_left 4
  have hao : Odd a := Nat.not_even_iff_odd.mp
    (mt even_iff_two_dvd.mp (Nat.not_dvd_ordCompl Nat.prime_two hN.ne'))
  have ha3 : a.factorization 3 = N.factorization 3 := by
    dsimp only [a]
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne (by decide : (3 : ℕ) ≠ 2)]
  have hsa := sigmaBiunitary_mul_of_coprime ha2
  rw [hna, sigmaBiunitary_sixteen, hσ] at hsa
  have hsa' : 27 * sigmaBiunitary a = 48 * a := by omega
  let m := ordCompl[3] a
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos 3 ha0).ne'
  have ham : 3 ^ N.factorization 3 * m = a := by
    simpa only [m, ha3] using Nat.ordProj_mul_ordCompl_eq_self a 3
  have hmo : Odd m := Nat.Odd.of_mul_right (ham ▸ hao)
  have hm3 : (3 ^ N.factorization 3).Coprime m :=
    (Nat.coprime_ordCompl (by decide : Nat.Prime 3) ha0).pow_left _
  have hsm := sigmaBiunitary_mul_of_coprime hm3
  rw [ham] at hsm
  rw [hsm, ← ham] at hsa'
  have hcases : N.factorization 3 = 3 ∨ N.factorization 3 = 4 := by omega
  rcases hcases with h3 | h4
  · rw [h3, show (3 : ℕ) ^ 3 = 27 by decide, sigmaBiunitary_twentySeven] at hsa'
    have hm5 : m = 5 := eq_five_of_sigmaBiunitary_ratio hmo (by omega)
    rw [← hna, ← ham, h3, hm5]
    decide
  · rw [h4, show (3 : ℕ) ^ 4 = 81 by decide,
      show sigmaBiunitary 81 = 112 by decide] at hsa'
    have hratio : 7 * sigmaBiunitary m = 9 * m := by omega
    have hso : Odd (sigmaBiunitary m) := Nat.Odd.of_mul_right (by
      rw [hratio]
      exact (by decide : Odd (9 : ℕ)).mul hmo)
    have hm1 : m = 1 := by
      by_contra hm1
      exact Nat.not_even_iff_odd.mpr hso (even_sigmaBiunitary_of_odd_pos hmo (by omega))
    rw [hm1, sigmaBiunitary_one] at hratio
    omega

end MetaMathlibExt
