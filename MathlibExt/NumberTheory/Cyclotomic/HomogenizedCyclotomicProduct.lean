/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomic

/-!
# Factorization into homogenized cyclotomic values

The product of the homogenized cyclotomic values over the divisors of a positive integer
`n` equals the difference of the `n`-th powers of their arguments.
-/

namespace MetaMathlibExt

open Polynomial

private theorem homogenizedCyclotomic_zero_right (n : ℕ) (a : ℤ) :
    homogenizedCyclotomic n a 0 = a ^ n.totient := by
  rw [homogenizedCyclotomic, Finset.sum_range_succ]
  have hcoeff := (cyclotomic.monic n ℤ).coeff_natDegree
  rw [natDegree_cyclotomic] at hcoeff
  rw [Finset.sum_eq_zero, hcoeff]
  · simp
  · intro i hi
    simp [zero_pow (Nat.sub_pos_of_lt (Finset.mem_range.mp hi)).ne']

/-- **Factorization of $a^n - b^n$ into homogenized cyclotomic values.** For every positive
integer $n$ and all integers $a$ and $b$,
$$a^n - b^n = \prod_{d \mid n} \Phi_d(a, b),$$
where the product runs over the positive divisors $d$ of $n$ and $\Phi_d(a, b)$ is the
homogenized cyclotomic value.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (i)
(quoted from reference [6]). -/
public theorem prod_divisors_homogenizedCyclotomic {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    ∏ d ∈ n.divisors, homogenizedCyclotomic d a b = a ^ n - b ^ n := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [homogenizedCyclotomic_zero_right, Finset.prod_pow_eq_pow_sum, Nat.sum_totient,
      zero_pow hn.ne', sub_zero]
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  apply Int.cast_injective (α := ℚ)
  push_cast
  simp_rw [homogenizedCyclotomic_cast (K := ℚ) _ _ _ hb']
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Nat.sum_totient, ← eval_prod,
    prod_cyclotomic_eq_X_pow_sub_one hn, eval_sub, eval_pow, eval_X, eval_one, div_pow, mul_sub,
    mul_div_cancel₀ _ (pow_ne_zero n hb'), mul_one]

end MetaMathlibExt
