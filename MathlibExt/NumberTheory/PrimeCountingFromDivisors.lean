/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Prime counting from the exact divisor count

The theorem `MetaMathlibExt.primeCountingApprox_sub_lt` bounds the difference between
the sum of exponential weights from divisor counts and the prime-counting function.
-/

namespace MetaMathlibExt

open Finset

private theorem three_le_card_divisors_of_composite {m : ℕ} (hm : 2 ≤ m)
    (hp : ¬ m.Prime) : 3 ≤ m.divisors.card := by
  obtain ⟨d, hd, hd₁, hdm⟩ := Nat.exists_dvd_of_not_prime hm hp
  have hm₀ : m ≠ 0 := by omega
  have hsub : ({1, d, m} : Finset ℕ) ⊆ m.divisors := by
    simp [insert_subset_iff, Nat.mem_divisors, hm₀, hd]
  simpa [Ne.symm hd₁, show 1 ≠ m by omega, hdm] using card_le_card hsub

/-- **Prime counting from the exact divisor count.** For every natural number $n \ge 2$,
$$\sum_{m=2}^{n} e^{-m(\tau(m) - 2)} - \pi(n) < \frac{1}{e^3(e - 1)},$$
where $\tau(m)$ is the number of positive divisors of $m$ and $\pi(n)$ is the number of primes at
most $n$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 3 (`integers-2026-A46-lem-3`). -/
public theorem primeCountingApprox_sub_lt (n : ℕ) (hn : 2 ≤ n) :
    ∑ m ∈ Icc 2 n, Real.exp (-(m * ((m.divisors.card : ℝ) - 2))) - Nat.primeCounting n <
      1 / (Real.exp 3 * (Real.exp 1 - 1)) := by
  let weight (m : ℕ) := Real.exp (-(m * ((m.divisors.card : ℝ) - 2)))
  let composites := (Icc 2 n).filter (fun m => ¬ m.Prime)
  have hprime : ∑ m ∈ n.primesLE, weight m = (Nat.primeCounting n : ℝ) := by
    calc
      _ = ∑ _m ∈ n.primesLE, (1 : ℝ) := by
        apply sum_congr rfl
        intro m hm
        have hp := Nat.prime_of_mem_primesLE hm
        simp [weight, hp.divisors, Ne.symm hp.ne_one]
      _ = _ := by simp
  have hsplit := sum_filter_add_sum_filter_not (Icc 2 n) Nat.Prime (f := weight)
  rw [← Nat.primesLE_eq_filter_Icc_two, hprime] at hsplit
  change ∑ m ∈ Icc 2 n, weight m - (Nat.primeCounting n : ℝ) < _
  rw [← hsplit, add_sub_cancel_left]
  have hratio : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  calc
    ∑ m ∈ composites, weight m ≤ ∑ m ∈ composites, Real.exp (-1) ^ m := by
      apply sum_le_sum
      intro m hm
      obtain ⟨hm, hp⟩ := mem_filter.mp hm
      have hcard : (3 : ℝ) ≤ m.divisors.card := by
        exact_mod_cast three_le_card_divisors_of_composite (mem_Icc.mp hm).1 hp
      dsimp only [weight]
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ (m.divisors.card : ℝ) - 2 by linarith)
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      linarith only [hmul]
    _ ≤ ∑ m ∈ Ico 4 (n + 2), Real.exp (-1) ^ m := by
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
      intro m hm
      obtain ⟨hm, hp⟩ := mem_filter.mp hm
      obtain ⟨hm₂, hmn⟩ := mem_Icc.mp hm
      have hne₂ : m ≠ 2 := by
        rintro rfl
        exact hp Nat.prime_two
      have hne₃ : m ≠ 3 := by
        rintro rfl
        exact hp Nat.prime_three
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    _ < Real.exp (-1) ^ 4 / (1 - Real.exp (-1)) := by
      rw [geom_sum_Ico' hratio.ne (by omega : 4 ≤ n + 2)]
      exact div_lt_div_of_pos_right (sub_lt_self _ (by positivity)) (sub_pos.mpr hratio)
    _ = _ := by
      rw [← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * (-1) = -(3 + 1) by norm_num,
        Real.exp_neg, Real.exp_add, Real.exp_neg]
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
      field_simp

end MetaMathlibExt
