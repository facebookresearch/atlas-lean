/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Ring

/-!
# Central binomial polynomial identity in Bernstein form

Kunle Adegoke, *A Short Proof of Knuth's Old Sum*, equation (7.12) of the preprint.
<https://arxiv.org/html/2412.00040#S7.E12>

With `a = (1 - x) / 2`, the quadratics `a (1 + X)² + x X` and `a (1 + X²) + X` agree.
Extracting the middle coefficient of their `n`th powers gives the two binomial sums.
-/

namespace MetaMathlibExt

open Finset Polynomial

private theorem coeff_pow_add_C_mul_X (n : ℕ) (a b : ℂ) (p : ℂ[X]) :
    ((C a * p + C b * X) ^ n).coeff n =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * a ^ k * b ^ (n - k) * (p ^ k).coeff k := by
  rw [add_pow, finsetSum_coeff]
  apply sum_congr rfl
  intro k hk
  have hkn := Nat.le_of_lt_succ (mem_range.mp hk)
  rw [coeff_mul_natCast, mul_pow, mul_pow, mul_mul_mul_comm, ← C_pow, ← C_pow, ← C_mul,
    coeff_C_mul, coeff_mul_X_pow', ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hkn]
  ring

/-- **Central binomial polynomial identity, Bernstein form.** For every natural number $n$ and
every complex $x$,
$$\sum_{k=0}^{n} \binom{n}{k} 2^{-k} \binom{2k}{k} (1-x)^k x^{n-k} =
\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} 2^{-2k} \binom{2k}{k} (1-x)^{2k}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 6 (`integers-2026-A19-cor-6`). -/
public theorem sum_choose_centralBinom_one_sub_pow_mul_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) * (1 - x) ^ k * x ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) * (1 - x) ^ (2 * k) := by
  let a := (1 - x) / 2
  have ha : 2 * a + x = 1 := by
    dsimp [a]
    ring
  have hquad : C a * (1 + X) ^ 2 + C x * X =
      C a * (1 + X ^ 2) + C (1 : ℂ) * X := by
    rw [← ha, map_add, map_mul, map_ofNat]
    ring
  calc
    _ = ((C a * (1 + X) ^ 2 + C x * X) ^ n).coeff n := by
      rw [coeff_pow_add_C_mul_X]
      apply sum_congr rfl
      intro k _
      rw [← pow_mul, coeff_one_add_X_pow]
      simp only [a, div_pow]
      ring
    _ = ((C a * (1 + X ^ 2) + C (1 : ℂ) * X) ^ n).coeff n := by rw [hquad]
    _ = _ := by
      rw [coeff_pow_add_C_mul_X]
      have hexpand (k : ℕ) : (1 + X ^ 2 : ℂ[X]) ^ k = expand ℂ 2 ((1 + X) ^ k) := by
        simp
      simp only [hexpand, coeff_expand (by decide : 0 < 2), coeff_one_add_X_pow, one_pow, mul_one]
      symm
      apply sum_of_injOn (fun j ↦ 2 * j)
      · exact (mul_right_injective₀ (two_ne_zero (α := ℕ))).injOn
      · intro j hj
        simp only [coe_range, Set.mem_Iio] at hj ⊢
        omega
      · intro k hk hmiss
        have hklt := mem_range.mp hk
        have hodd : ¬ 2 ∣ k := by
          rintro ⟨j, rfl⟩
          exact hmiss ⟨j, mem_range.mpr (by omega), rfl⟩
        simp [hodd]
      · intro j _
        simp only [dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
          a, div_pow]
        ring

/-- **Even-index binomial sum equal to a scaled central binomial coefficient.** For every
natural number $n$,
$$\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \frac{1}{2^{2k}} \binom{2k}{k} =
\frac{1}{2^n} \binom{2n}{n}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 4 (`integers-2026-A19-prop-4`). -/
public theorem sum_choose_even_centralBinom_div_four_pow (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) =
      ((2 * n).choose n : ℚ) / 2 ^ n := by
  have h := sum_choose_centralBinom_one_sub_pow_mul_pow n 0
  simp only [sub_zero, one_pow, mul_one] at h
  have hzero :
      (∑ k ∈ range (n + 1), (n.choose k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) * 0 ^ (n - k)) =
        ((2 * n).choose n : ℂ) / 2 ^ n := by
    rw [sum_eq_single_of_mem n (mem_range.mpr (Nat.lt_succ_self n))]
    · simp [div_eq_mul_inv, mul_comm]
    · intro k hk hkn
      have hlt := lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hk)) hkn
      simp [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))]
  rw [hzero] at h
  apply (Rat.cast_injective (α := ℂ))
  change (Rat.castHom ℂ) _ = (Rat.castHom ℂ) _
  simpa only [map_sum, map_mul, map_div₀, map_pow, map_natCast, map_ofNat] using h.symm

/-- **Even-index expansion of a weighted central binomial sum.** For every natural number $n$,
$$\sum_{k=0}^{n} \binom{n}{k} 2^{-k} \binom{2k}{k} =
\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} 2^{n-4k} \binom{2k}{k}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 5 (`integers-2026-A19-prop-5`). -/
public theorem sum_choose_centralBinom_div_two_pow (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) / 2 ^ k * ((2 * k).choose k : ℚ) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℚ) * 2 ^ n / 2 ^ (4 * k) * ((2 * k).choose k : ℚ) := by
  apply (Rat.cast_injective (α := ℂ))
  change (Rat.castHom ℂ) _ = (Rat.castHom ℂ) _
  simp only [map_sum, map_mul, map_div₀, map_pow, map_natCast, map_ofNat]
  have hhalf : 1 - (1 / 2 : ℂ) = 1 / 2 := by ring
  have h := sum_choose_centralBinom_one_sub_pow_mul_pow n (1 / 2)
  rw [hhalf] at h
  calc
    _ = (∑ k ∈ range (n + 1),
          (n.choose k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) * (1 / 2) ^ k * (1 / 2) ^ (n - k)) *
          2 ^ n := by
      rw [sum_mul]
      apply sum_congr rfl
      intro k hk
      have hkn := Nat.le_of_lt_succ (mem_range.mp hk)
      rw [mul_assoc (_ / _ * _), ← pow_add, Nat.add_sub_of_le hkn, mul_assoc, ← mul_pow,
        div_mul_cancel₀ _ (two_ne_zero : (2 : ℂ) ≠ 0), one_pow, mul_one]
    _ = (∑ k ∈ range (n / 2 + 1),
          (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) * (1 / 2) ^ (2 * k)) *
          2 ^ n := by rw [h]
    _ = _ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro k _
      rw [show 4 * k = 2 * k + 2 * k by omega, pow_add, div_pow, one_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end MetaMathlibExt
