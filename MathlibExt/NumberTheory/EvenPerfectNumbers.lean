/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Fermat

@[expose] public section

namespace MetaMathlibExt

private theorem sum_divisors_two_pow (k : ℕ) :
    ∑ d ∈ (2 ^ k).divisors, d = 2 ^ (k + 1) - 1 := by
  have h1 : ∑ x ∈ Finset.range (k + 1), 2 ^ x = 2 ^ (k + 1) - 1 := by
    have h2 := Nat.geomSum_eq (m := 2) (by norm_num) (k + 1)
    simpa using h2
  have h0 : (∑ d ∈ (2 ^ k).divisors, d) = ∑ x ∈ Finset.range (k + 1), 2 ^ x :=
    Nat.sum_divisors_prime_pow Nat.prime_two
  rw [h0]
  exact h1

/--
**Euler's theorem on even perfect numbers.** Every even perfect number $N$ is of the form
$N = 2^{p-1}(2^p - 1)$ for some natural number $p$ such that $p$ and $2^p - 1$ are both prime.

Source: Paulo J. Almeida and Gabriel Cardoso,
"An Extension of the Euclid-Euler Theorem to Certain α-Perfect Numbers,"
Journal of Integer Sequences 25 (2022), Article 22.8.4,
Theorem [Euler] (unlabeled), lines 164–166,
https://cs.uwaterloo.ca/journals/JIS/VOL25/Almeida/almeida9.tex
-/
theorem euler_characterization_of_even_perfect_numbers
    (N : ℕ)
    (hN_even : Even N)
    (hN_perfect : Nat.Perfect N) :
    ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (2 ^ p - 1) ∧
      N = 2 ^ (p - 1) * (2 ^ p - 1) := by
  obtain ⟨hsum, hpos⟩ := hN_perfect
  obtain ⟨k, m, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (ne_of_gt hpos)
  have hm_ne : m ≠ 0 := by
    rintro rfl
    simp at hpos
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · have hevm : Even m := by simpa using hN_even
      exact absurd hevm (Nat.not_even_iff_odd.mpr hodd)
    · exact h
  have hcop : Nat.Coprime (2 ^ k) m := hodd.coprime_two_right.symm.pow_left k
  have hperf : ∑ d ∈ (2 ^ k * m).divisors, d = 2 * (2 ^ k * m) :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp ⟨hsum, hpos⟩
  set q := 2 ^ (k + 1) - 1 with hq
  have h2k4 : 4 ≤ 2 ^ (k + 1) :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq3 : 3 ≤ q := by omega
  have h2k : 2 ^ (k + 1) = q + 1 := by omega
  have hσ : q * (∑ d ∈ m.divisors, d) = (q + 1) * m := by
    have h1 := Nat.Coprime.sum_divisors_mul hcop
    rw [sum_divisors_two_pow, ← hq, hperf] at h1
    have h2 : 2 * (2 ^ k * m) = (q + 1) * m := by
      rw [← h2k, pow_succ']
      ring
    exact h1.symm.trans h2
  have hqcop : Nat.Coprime q (q + 1) := by simp
  have hqdvd : q ∣ (q + 1) * m := ⟨∑ d ∈ m.divisors, d, hσ.symm⟩
  have hqm : q ∣ m := hqcop.dvd_mul_left.mp hqdvd
  obtain ⟨t, rfl⟩ := hqm
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hm_ne
    · exact h
  have hq0 : q ≠ 0 := by omega
  have hS : ∑ d ∈ (q * t).divisors, d = (q + 1) * t := by
    apply mul_left_cancel₀ hq0
    calc q * ∑ d ∈ (q * t).divisors, d = (q + 1) * (q * t) := hσ
      _ = q * ((q + 1) * t) := by ring
  have hSt : ∑ d ∈ (q * t).divisors, d = q * t + t := by
    rw [hS]
    ring
  have hP : ∑ i ∈ (q * t).properDivisors, i = t := by
    have h := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := q * t)
    omega
  have htm : t < q * t := lt_mul_of_one_lt_left ht0 (by omega)
  have ht_mem : t ∈ (q * t).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨dvd_mul_left t q, htm⟩
  have h1_mem : 1 ∈ (q * t).properDivisors := by
    rw [Nat.one_mem_properDivisors_iff_one_lt]
    have e := Nat.mul_le_mul (by omega : (2 : ℕ) ≤ q) (by omega : (1 : ℕ) ≤ t)
    omega
  have ht1 : t = 1 := by
    by_contra hne
    have hsub : ({1, t} : Finset ℕ) ⊆ (q * t).properDivisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1_mem
      · exact ht_mem
    have hle : (1 : ℕ) + t ≤ ∑ i ∈ (q * t).properDivisors, i := by
      calc (1 : ℕ) + t = ∑ x ∈ ({1, t} : Finset ℕ), x :=
            (Finset.sum_pair (f := fun x => x) (Ne.symm hne)).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le i)
    omega
  subst ht1
  rw [mul_one] at hP
  have hq_prime : q.Prime := Nat.sum_properDivisors_eq_one_iff_prime.mp hP
  have hp_prime : (k + 1).Prime := by
    have hM : ((2 : ℕ) ^ (k + 1) - 1).Prime := by
      rw [← hq]
      exact hq_prime
    exact (Nat.prime_of_pow_sub_one_prime (by omega) hM).2
  refine ⟨k + 1, hp_prime, ?_, ?_⟩
  · rw [← hq]
    exact hq_prime
  · rw [Nat.add_sub_cancel, mul_one, ← hq]

end MetaMathlibExt
