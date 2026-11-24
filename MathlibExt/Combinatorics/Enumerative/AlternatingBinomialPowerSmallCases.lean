/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumStirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Small cases of alternating binomial power sums

The diagonal and subdiagonal follow from the Stirling expansion. The row sum telescopes
by the order recurrence with the shift parameter `y - x`.
-/

namespace MetaMathlibExt

open Finset

-- At degree `n + 1` and order `n`, only the last two terms of the Stirling expansion occur.
private theorem alternatingBinomialPowerSum_subdiagonal (x y : ℂ) (n : ℕ) :
    alternatingBinomialPowerSum (n + 1) n x y =
      (-1) ^ n * ((n + 1).factorial : ℂ) * x ^ n * (y + (n : ℂ) / 2 * x) := by
  have hinterval : Icc n (n + 1) = {n, n + 1} := by
    ext j
    simp only [mem_Icc, mem_insert, mem_singleton]
    omega
  have hchoose : ((n + 1).choose 2 : ℂ) = ((n : ℂ) + 1) * n / 2 := by
    have h := Nat.add_one_mul_choose_eq n 1
    rw [Nat.choose_one_right] at h
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    exact_mod_cast h.symm
  rw [(alternatingBinomialPowerSum_eq_sum_stirlingSecond x y (n + 1) n).1,
    hinterval, sum_pair (Nat.ne_of_lt (Nat.lt_succ_self n))]
  simp only [Nat.choose_succ_self_right, Nat.choose_self, Nat.stirlingSecond_self,
    Nat.stirlingSecond_succ_self_left, Nat.add_sub_cancel_left, Nat.sub_self, pow_one, pow_zero,
    mul_one, hchoose, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ x n]
  ring

/-- **Small cases of alternating binomial power sums.** Let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (kx + y)^\ell$, with $0^0 = 1$. For all
complex numbers $x, y$ and natural numbers $\ell, m$:
(i) $p_{\ell,0}(x, y) = y^\ell$;
(ii) $p_{\ell,1}(x, y) = y^\ell - (x + y)^\ell$;
(iii) $p_{\ell,2}(x, y) = y^\ell - 2(x + y)^\ell + (2x + y)^\ell$;
(iv) if $\ell \ge 1$, then
$p_{\ell,\ell-1}(x, y) = (-1)^{\ell-1} \ell!\, x^{\ell-1} \left(y + \frac{\ell - 1}{2} x\right)$;
(v) $p_{\ell,\ell}(x, y) = (-1)^\ell \ell!\, x^\ell$;
(vi) $p_{0,m}(x, y) = 0^m$;
(vii) $\sum_{m=0}^{\ell} p_{\ell,m}(x, y) = (y - x)^\ell$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 3 (`integers-2024-A70-prop-3`). -/
public theorem alternatingBinomialPowerSum_small_cases (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ 0 x y = y ^ ℓ ∧
      alternatingBinomialPowerSum ℓ 1 x y = y ^ ℓ - (x + y) ^ ℓ ∧
      alternatingBinomialPowerSum ℓ 2 x y = y ^ ℓ - 2 * (x + y) ^ ℓ + (2 * x + y) ^ ℓ ∧
      (1 ≤ ℓ → alternatingBinomialPowerSum ℓ (ℓ - 1) x y =
        (-1) ^ (ℓ - 1) * (ℓ.factorial : ℂ) * x ^ (ℓ - 1) * (y + ((ℓ : ℂ) - 1) / 2 * x)) ∧
      alternatingBinomialPowerSum ℓ ℓ x y = (-1) ^ ℓ * (ℓ.factorial : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum 0 m x y = 0 ^ m ∧
      ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m x y = (y - x) ^ ℓ := by
  have hzero (z : ℂ) : alternatingBinomialPowerSum ℓ 0 x z = z ^ ℓ := by
    simp [alternatingBinomialPowerSum]
  refine ⟨hzero y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [alternatingBinomialPowerSum, sum_range_succ, sub_eq_add_neg]
  · norm_num [alternatingBinomialPowerSum, sum_range_succ, Nat.choose, sub_eq_add_neg]
  · intro hℓ
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
    simpa using alternatingBinomialPowerSum_subdiagonal x y n
  · simpa [mul_right_comm] using
      (alternatingBinomialPowerSum_eq_sum_stirlingSecond x y ℓ ℓ).2.2
  · simpa [alternatingBinomialPowerSum] using (add_pow (-1 : ℂ) 1 m).symm
  · have hstep (k : ℕ) : alternatingBinomialPowerSum ℓ k x y =
        alternatingBinomialPowerSum ℓ k x (y - x) -
          alternatingBinomialPowerSum ℓ (k + 1) x (y - x) := by
      rw [(alternatingBinomialPowerSum_recurrences x (y - x) ℓ k).1,
        add_sub_cancel x y, sub_sub_cancel]
    simp_rw [hstep, sum_range_sub']
    rw [hzero, (alternatingBinomialPowerSum_eq_sum_stirlingSecond x (y - x) ℓ (ℓ + 1)).2.1
      (Nat.lt_succ_self ℓ), sub_zero]

end MetaMathlibExt
