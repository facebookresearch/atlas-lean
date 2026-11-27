/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.PerturbedTailProduct

open Filter Asymptotics

-- With c = -1 the linear tail is positive. The perturbation makes the initial
-- factor zero and thereafter decays at the limiting rate allowed by the hypothesis.
example :
    let e (k : ℕ) := if k = 0 then (-2 : ℝ) else (1 / 16 : ℝ) ^ k
    (fun n : ℕ ↦ (∏' k : ℕ, (1 + (1 / 8 : ℝ) ^ (n + k) + e (n + k))) -
      (1 + 8 / 7 * (1 / 8 : ℝ) ^ n)) =O[atTop] fun n : ℕ ↦ (1 / 16 : ℝ) ^ n := by
  intro e
  have hrate (k : ℕ) : ((2 : ℝ) / 8 ^ 3) ^ ((k : ℝ) / 2) = (1 / 16 : ℝ) ^ k := by
    rw [show (k : ℝ) / 2 = (1 / 2 : ℝ) * k by ring, Real.rpow_mul_natCast (by norm_num),
      ← Real.sqrt_eq_rpow]
    congr 1
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have he : e =O[atTop] fun k : ℕ ↦ ((2 : ℝ) / 8 ^ 3) ^ ((k : ℝ) / 2) := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_gt_atTop 0] with k hk
    simp [e, hk.ne', hrate]
  have h := MetaMathlibExt.tprod_one_sub_inv_add_eq_one_sub_tsum_add_isBigO
    (-1) 8 2 (by norm_num) (by norm_num) (by norm_num) e he
  have htail (n : ℕ) : (∑' k : ℕ, (1 / 8 : ℝ) ^ (n + k)) = 8 / 7 * (1 / 8 : ℝ) ^ n := by
    simp_rw [pow_add, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 8 : ℝ))
      (by norm_num)]
    ring
  have hterm (k : ℕ) : 1 / ((-1 : ℝ) * 8 ^ k) = -((1 / 8 : ℝ) ^ k) := by
    rw [neg_one_mul, div_neg, one_div_pow]
  simpa only [hrate, hterm, sub_neg_eq_add, tsum_neg, htail] using h
