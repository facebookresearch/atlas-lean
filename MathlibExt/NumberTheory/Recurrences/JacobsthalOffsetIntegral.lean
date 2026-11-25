/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.Recurrences.KJacobsthal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# An integral representation of Jacobsthal numbers with an offset

We express the Jacobsthal number at index `ℓ * n + r` as an interval integral on `[-1, 1]`.
-/

namespace MetaMathlibExt

open MeasureTheory

local notation "J[" k ", " n "]" => (lucasU (kJacobsthalParams k) n : ℝ)
local notation "jL[" k ", " n "]" => (lucasV (kJacobsthalParams k) n : ℝ)

-- The primitive is (d / 3 + c * x) * (b + 3 * a * x) ^ n.
private theorem jacobsthal_mul_add_eq_integral.integral_kernel (a b c d : ℝ)
    (h : b + 3 * a ≠ 0) (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (n * a * d + c * b + 3 * (n + 1) * a * c * x) *
      (b + 3 * a * x) ^ ((n : ℤ) - 1)) =
      (d / 3 + c) * (b + 3 * a) ^ n - (d / 3 - c) * (b - 3 * a) ^ n := by
  cases n with
  | zero =>
    -- The affine denominator can vanish at a single point in the interval.
    have hne : ∀ᵐ x : ℝ, b + 3 * a * x ≠ 0 := by
      by_cases ha : 3 * a = 0
      · simpa [ha] using h
      · filter_upwards [volume.ae_ne (-b / (3 * a))] with x hx
        exact fun hz => hx ((eq_div_iff ha).2 (by linarith))
    calc
      _ = ∫ _ in (-1 : ℝ)..1, c := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hne] with x hx
        intro _
        simp only [Nat.cast_zero, zero_mul, zero_add, zero_sub, zpow_neg_one]
        field_simp
      _ = _ := by simp [intervalIntegral.integral_const]; ring
  | succ n =>
    simp only [Nat.cast_succ, add_sub_cancel_right, zpow_natCast]
    let F := fun x : ℝ => (d / 3 + c * x) * (b + 3 * a * x) ^ (n + 1)
    calc
      _ = F 1 - F (-1) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro x _
          have hlin (u v : ℝ) : HasDerivAt (fun y => u + v * y) v x := by
            simpa using ((hasDerivAt_id x).const_mul v).const_add u
          convert (hlin (d / 3) c).fun_mul ((hlin b (3 * a)).fun_pow (n + 1)) using 1
          simp only [Nat.add_sub_cancel, Nat.cast_succ, pow_succ]
          ring
        · apply Continuous.intervalIntegrable
          fun_prop
      _ = _ := by simp [F, sub_eq_add_neg]

/-- **Integral representation of Jacobsthal numbers with an offset.** Let $\ell$, $n$ and $r$ be
natural numbers and let $J_n = U_n(1, -2)$ and $j_n = V_n(1, -2)$ be the Jacobsthal and
Jacobsthal–Lucas numbers (the case $k = 1$). Then
$$J_{\ell n + r} = \frac{1}{2^{n+1}} \int_{-1}^{1}
(n J_\ell j_r + J_r j_\ell + 3(n+1) J_\ell J_r x) (j_\ell + 3 J_\ell x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 4 (`integers-2025-A74-cor-4`). -/
public theorem jacobsthal_mul_add_eq_integral (ℓ n r : ℕ) :
    (lucasU (kJacobsthalParams 1) (ℓ * n + r) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (n * J[1, ℓ] * jL[1, r] + J[1, r] * jL[1, ℓ] +
            3 * (n + 1) * J[1, ℓ] * J[1, r] * x) *
          (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1) := by
  have hbinet := (lucas_binet_formulas_of_field (kJacobsthalParams 1) (2 : ℝ) (-1)
    (by norm_num [kJacobsthalParams]) (by norm_num [kJacobsthalParams])).1 (by norm_num)
  have hplus (m : ℕ) : jL[1, m] + 3 * J[1, m] = 2 * 2 ^ m := by
    rw [(hbinet m).1, (hbinet m).2]
    ring
  have hminus (m : ℕ) : jL[1, m] - 3 * J[1, m] = 2 * (-1) ^ m := by
    rw [(hbinet m).1, (hbinet m).2]
    ring
  rw [jacobsthal_mul_add_eq_integral.integral_kernel _ _ _ _ (by rw [hplus]; positivity),
    hplus ℓ, hminus ℓ, (hbinet (ℓ * n + r)).1]
  have hr₁ := hplus r
  have hr₂ := hminus r
  rw [show jL[1, r] / 3 + J[1, r] = 2 * 2 ^ r / 3 by linarith,
    show jL[1, r] / 3 - J[1, r] = 2 * (-1) ^ r / 3 by linarith]
  simp only [pow_add, pow_mul, mul_pow, pow_one]
  field_simp
  ring

end MetaMathlibExt
