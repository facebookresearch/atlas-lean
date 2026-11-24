/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Deficiency of odd numbers with two distinct prime factors -/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

private theorem geom_sum_div_pow_lt (r : ℚ) (hr : 1 < r) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), r ^ i) / r ^ k < r / (r - 1) := by
  have hrk : 0 < r ^ k := pow_pos (by positivity) _
  rw [div_lt_div_iff₀ hrk (sub_pos.mpr hr), geom_sum_mul, pow_succ]
  rw [mul_comm r]
  exact sub_lt_self _ zero_lt_one

private theorem prime_ratio_le {r s : ℚ} (hs : 1 < s) (hsr : s ≤ r) :
    r / (r - 1) ≤ s / (s - 1) := by
  rw [div_le_div_iff₀ (sub_pos.mpr (hs.trans_le hsr)) (sub_pos.mpr hs)]
  linarith

/-- **Odd numbers with two prime factors are deficient.** If $n$ is an odd natural number with
exactly two distinct prime divisors, then $\sigma(n) < 2n$, where $\sigma(n)$ is the sum of the
positive divisors of $n$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma
(label `Classificationofprimitivenondeficientwhenkis2`), second
part. -/
public theorem deficient_of_odd_card_primeFactors_eq_two
    (n : ℕ) (hno : Odd n) (hk : n.primeFactors.card = 2) :
    ∑ d ∈ Nat.divisors n, d < 2 * n := by
  obtain ⟨p, q, hpq, hf⟩ : ∃ p q : ℕ, p < q ∧ n.primeFactors = {p, q} := by
    obtain ⟨a, b, hab, h⟩ := Finset.card_eq_two.mp hk
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨a, b, hab, h⟩
    · exact ⟨b, a, hba, h.trans (Finset.pair_comm _ _)⟩
  have odd_factor (r : ℕ) (hr : r ∈ n.primeFactors) : Odd r := by
    apply (Nat.prime_of_mem_primeFactors hr).odd_of_ne_two
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hno) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hr))
  have hp : 3 ≤ p := by
    have hpm : p ∈ n.primeFactors := by simp [hf]
    have hp2 := (Nat.prime_of_mem_primeFactors hpm).two_le
    obtain ⟨a, ha⟩ := odd_factor p hpm
    omega
  have hq : 5 ≤ q := by
    obtain ⟨b, hb⟩ := odd_factor q (by simp [hf])
    omega
  have hrp : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hrq : (5 : ℚ) ≤ q := by exact_mod_cast hq
  have hn : n ≠ 0 := hno.pos.ne'
  have hprod : (n : ℚ) = ∏ r ∈ n.primeFactors, (r : ℚ) ^ n.factorization r := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  have habund : (↑(∑ d ∈ Nat.divisors n, d) : ℚ) / n =
      ∏ r ∈ n.primeFactors,
        (∑ i ∈ Finset.range (n.factorization r + 1), (r : ℚ) ^ i) /
          (r : ℚ) ^ n.factorization r := by
    rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
    simp only [mul_one, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow]
    rw [Finset.prod_div_distrib, ← hprod]
  have hlt : (↑(∑ d ∈ Nat.divisors n, d) : ℚ) / n < 2 := by
    rw [habund, hf, Finset.prod_pair hpq.ne]
    calc
      _ ≤ (3 / 2 : ℚ) * (5 / 4) := by
        apply mul_le_mul
        · exact (geom_sum_div_pow_lt (p : ℚ) (by linarith) _).le.trans
            (by simpa only [show (3 : ℚ) - 1 = 2 by norm_num] using
              prime_ratio_le (by norm_num) hrp)
        · exact (geom_sum_div_pow_lt (q : ℚ) (by linarith) _).le.trans
            (by simpa only [show (5 : ℚ) - 1 = 4 by norm_num] using
              prime_ratio_le (by norm_num) hrq)
        · exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
        · positivity
      _ < 2 := by norm_num
  have hnq : (0 : ℚ) < n := by exact_mod_cast hno.pos
  exact_mod_cast (div_lt_iff₀ hnq).mp hlt

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
