/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.EulerPrime

/-! # The exponent of five in odd perfect multiples of 165 -/

namespace MetaMathlibExt

open Finset

private theorem sum_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ range (k + 1), p ^ i := by
  rw [← ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply_prime_pow hp]

private theorem sum_divisors_70785 : ∑ d ∈ (70785 : ℕ).divisors, d = 145236 := by
  rw [← show (3 ^ 2 * 5 ^ 1 * 11 ^ 2 * 13 ^ 1 : ℕ) = 70785 by norm_num]
  rw [Nat.Coprime.sum_divisors_mul (m := 3 ^ 2 * 5 ^ 1 * 11 ^ 2) (n := 13 ^ 1) (by decide),
    Nat.Coprime.sum_divisors_mul (m := 3 ^ 2 * 5 ^ 1) (n := 11 ^ 2) (by decide),
    Nat.Coprime.sum_divisors_mul (m := 3 ^ 2) (n := 5 ^ 1) (by decide),
    sum_divisors_prime_pow (p := 3) (by decide), sum_divisors_prime_pow (p := 5) (by decide),
    sum_divisors_prime_pow (p := 11) (by decide), sum_divisors_prime_pow (p := 13) (by decide)]
  norm_num [sum_range_succ]

private theorem sum_divisors_245025 : ∑ d ∈ (245025 : ℕ).divisors, d = 498883 := by
  rw [← show (3 ^ 4 * 5 ^ 2 * 11 ^ 2 : ℕ) = 245025 by norm_num]
  rw [Nat.Coprime.sum_divisors_mul (m := 3 ^ 4 * 5 ^ 2) (n := 11 ^ 2) (by decide),
    Nat.Coprime.sum_divisors_mul (m := 3 ^ 4) (n := 5 ^ 2) (by decide),
    sum_divisors_prime_pow (p := 3) (by decide), sum_divisors_prime_pow (p := 5) (by decide),
    sum_divisors_prime_pow (p := 11) (by decide)]
  norm_num [sum_range_succ]

-- Scaling by the cofactor sends divisors of D injectively to divisors of n.
private theorem not_dvd_perfect_of_abundant {D n : ℕ} (hperf : n.Perfect)
    (hD : 2 * D < ∑ d ∈ D.divisors, d) : ¬ D ∣ n := by
  rintro ⟨c, rfl⟩
  have hc : 0 < c := Nat.pos_of_ne_zero fun hc ↦ hperf.2.ne' (by simp [hc])
  let f : ℕ ↪ ℕ := ⟨(· * c), fun _ _ h ↦ Nat.eq_of_mul_eq_mul_right hc h⟩
  have hsub : D.divisors.map f ⊆ (D * c).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := mem_map.mp hx
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors hd) c, hperf.2.ne'⟩
  have hle : (∑ d ∈ D.divisors, d) * c ≤ ∑ d ∈ (D * c).divisors, d := by
    calc
      (∑ d ∈ D.divisors, d) * c = ∑ x ∈ D.divisors.map f, x := by
        rw [sum_map, sum_mul]
        rfl
      _ ≤ _ := sum_le_sum_of_subset hsub
  rw [(Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf, ← mul_assoc] at hle
  exact (not_le_of_gt (Nat.mul_lt_mul_of_pos_right hD hc)) hle

/-- **Odd perfect numbers divisible by 165 contain 5 exactly once.** If $n$ is an odd perfect
number divisible by $165$, then $5$ divides $n$ exactly once: $5 \mid n$ but $25 \nmid n$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 11 (`integers-2025-A59-lem-11`). -/
public theorem oddPerfect_factorization_five_eq_one_of_dvd
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h165 : 165 ∣ n) :
    n.factorization 5 = 1 := by
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hn : n ≠ 0 := hperf.2.ne'
  have h3 : 3 ∣ n := (by decide : 3 ∣ 165).trans h165
  have h5 : 5 ∣ n := (by decide : 5 ∣ 165).trans h165
  have h11 : 11 ∣ n := (by decide : 11 ∣ 165).trans h165
  obtain ⟨q, s, m, hq, hform, hqmod, _, _⟩ := euler_odd_perfect_form n hodd hperf
  have hm : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hform)
  have hfac {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) :
      n.factorization p = 2 * m.factorization p := by
    have hpdvd : ¬ p ∣ q ^ s := fun hd ↦
      hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd))
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  have hq3 : 3 ≠ q := fun h ↦ (by decide : ¬ Nat.ModEq 4 3 1) (h ▸ hqmod)
  have hq11 : 11 ≠ q := fun h ↦ (by decide : ¬ Nat.ModEq 4 11 1) (h ▸ hqmod)
  have h3even := hfac hp3 hq3
  have h11even := hfac hp11 hq11
  have h3one : 1 ≤ n.factorization 3 := (hp3.pow_dvd_iff_le_factorization hn).mp (by simpa using h3)
  have h11one : 1 ≤ n.factorization 11 :=
    (hp11.pow_dvd_iff_le_factorization hn).mp (by simpa using h11)
  have h3sq : 3 ^ 2 ∣ n := (hp3.pow_dvd_iff_le_factorization hn).mpr (by omega)
  have h11sq : 11 ^ 2 ∣ n := (hp11.pow_dvd_iff_le_factorization hn).mpr (by omega)
  have h3four : 3 ^ 4 ∣ n := by
    by_contra hnot
    -- The prime-power divisor sum applies to the exact 3-part, not just a divisor 3².
    have h3exact : n.factorization 3 = 2 := by
      have hlt : ¬ 4 ≤ n.factorization 3 := mt (hp3.pow_dvd_iff_le_factorization hn).mpr hnot
      omega
    have hsplit : 3 ^ 2 * ordCompl[3] n = n := by
      rw [← h3exact]
      exact Nat.ordProj_mul_ordCompl_eq_self n 3
    have hsum := (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
    have hsum3 : ∑ d ∈ (3 ^ 2 : ℕ).divisors, d = 13 := by
      rw [sum_divisors_prime_pow hp3]
      norm_num [sum_range_succ]
    have h13twice : 13 ∣ 2 * n := by
      rw [← hsum, ← hsplit, (Nat.coprime_ordCompl hp3 hn).pow_left 2 |>.sum_divisors_mul, hsum3]
      exact dvd_mul_right _ _
    have h13 : 13 ∣ n := (hp13.dvd_mul.mp h13twice).resolve_left (by decide)
    have hD : 70785 ∣ n := by
      change 3 ^ 2 * 5 * 11 ^ 2 * 13 ∣ n
      exact (by decide : Nat.Coprime (3 ^ 2 * 5 * 11 ^ 2) 13).mul_dvd_of_dvd_of_dvd
        ((by decide : Nat.Coprime (3 ^ 2 * 5) (11 ^ 2)).mul_dvd_of_dvd_of_dvd
          ((by decide : Nat.Coprime (3 ^ 2) 5).mul_dvd_of_dvd_of_dvd h3sq h5) h11sq) h13
    exact not_dvd_perfect_of_abundant hperf (by rw [sum_divisors_70785]; decide) hD
  have h5sq : ¬ 5 ^ 2 ∣ n := by
    intro h25
    have hD : 245025 ∣ n := by
      change 3 ^ 4 * 5 ^ 2 * 11 ^ 2 ∣ n
      exact (by decide : Nat.Coprime (3 ^ 4 * 5 ^ 2) (11 ^ 2)).mul_dvd_of_dvd_of_dvd
        ((by decide : Nat.Coprime (3 ^ 4) (5 ^ 2)).mul_dvd_of_dvd_of_dvd h3four h25) h11sq
    exact not_dvd_perfect_of_abundant hperf (by rw [sum_divisors_245025]; decide) hD
  have hlo : 1 ≤ n.factorization 5 := (hp5.pow_dvd_iff_le_factorization hn).mp (by simpa using h5)
  have hhi : ¬ 2 ≤ n.factorization 5 := mt (hp5.pow_dvd_iff_le_factorization hn).mpr h5sq
  omega

end MetaMathlibExt
