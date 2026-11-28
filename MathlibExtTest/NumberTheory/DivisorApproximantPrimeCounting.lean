/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisorApproximantPrimeCounting

/-! # A concrete weight for the exponential divisor estimates -/

namespace MetaMathlibExt

open Asymptotics Filter Finset

-- The reciprocal of the squared sine saturates the hypothesis at every nondivisor.
private theorem inv_sin_sq_weight_bound :
    ∀ k n : ℕ, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ (Real.sin (n * Real.pi / k) ^ 2)⁻¹ * Real.sin (n * Real.pi / k) ^ 2 := by
  intro k n hk _ hnd
  have hs : Real.sin (n * Real.pi / k) ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hzero
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have heq : (n : ℝ) = k * z := by
      apply mul_right_cancel₀ Real.pi_ne_zero
      simpa only [mul_assoc, mul_comm, mul_left_comm] using ((eq_div_iff hk').mp hz).symm
    exact hnd (Int.natCast_dvd_natCast.mp ⟨z, by exact_mod_cast heq⟩)
  simp [hs]

example :
    (fun n : ℕ => ∑ k ∈ Icc 1 n,
      Real.exp (-(n * k * (Real.sin (n * Real.pi / k) ^ 2)⁻¹ * Real.sin (n * Real.pi / k) ^ 2)) -
        (n.divisors.card : ℝ)) =O[atTop] fun n : ℕ => 1 / (Real.exp n - 1) := by
  exact divisorCountApprox_sub_isBigO _ inv_sin_sq_weight_bound

-- With this weight, the hypothesis holds with equality at every nondivisor, and each nondivisor
-- weight is exactly `e^{-nk}`.
example (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    |Real.exp (-(n * k * (Real.sin (n * Real.pi / k) ^ 2)⁻¹ * Real.sin (n * Real.pi / k) ^ 2)) -
        (if k ∣ n then 1 else 0)| ≤ Real.exp (-(n * k : ℝ)) :=
  abs_exp_approx_sub_dvd_indicator_le _ inv_sin_sq_weight_bound k n hk hkn

-- At n = 3, only the nondivisor 2 contributes to the error in the divisor sum.
example : 2 * Real.exp (-6) < 3 / (Real.exp 3 - 1) := by
  have h := divisorSumApprox_sub_lt _ inv_sin_sq_weight_bound 3 (by decide)
  have hIcc : Icc 1 (3 : ℕ) = {1, 2, 3} := by decide
  have hdiv : (3 : ℕ).divisors = {1, 3} := by decide
  have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi, Real.sin_pi_div_two]
  have hsin₃ : Real.sin (3 * Real.pi) = 0 := Real.sin_nat_mul_pi 3
  norm_num [hIcc, hdiv, hsin, hsin₃, Real.sin_pi] at h
  linarith only [h]

-- The retained ATLAS weight satisfies the error estimate's hypothesis uniformly.
example :
    (fun n : ℕ => ∑ k ∈ Icc 1 n,
      Real.exp (-(n * k * (Real.pi ^ 2 * k ^ 2 / 2) * Real.sin (n * Real.pi / k) ^ 2)) -
        (n.divisors.card : ℝ)) =O[atTop] fun n : ℕ => 1 / (Real.exp n - 1) := by
  refine divisorCountApprox_sub_isBigO _ ?_
  intro k n hk hkn hnd
  exact one_le_pi_sq_mul_sq_div_two_mul_sin_sq k n hk (hk.trans hkn) hnd

-- The residue lies past the midpoint, and the statement does not require k ≤ n.
example : 1 ≤ Real.pi ^ 2 * (5 : ℝ) ^ 2 / 2 * Real.sin (4 * Real.pi / 5) ^ 2 :=
  one_le_pi_sq_mul_sq_div_two_mul_sin_sq 5 4 (by decide) (by decide) (by decide)

end MetaMathlibExt
