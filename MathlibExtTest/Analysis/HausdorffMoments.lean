/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HausdorffMoments

/-!
# Tests for Hausdorff positivity

A point mass at a mixed corner has a nonconstant moment sequence. In dimension one the
reverse direction yields a measure for the moments of the point mass at zero. In dimension
zero the sole moment can be any nonnegative real number.
-/

open MeasureTheory MathlibExt.Analysis.HausdorffMomentsWanted.Analysis

-- The two coordinates of this atom distinguish the zeroth and positive powers of zero.
example (k n : Fin 2 → ℕ) (h : k ≤ n) :
    0 ≤ diff (fun m : Fin 2 → ℕ => if m 0 = 0 then 1 else 0) k n := by
  classical
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hx : x ∈ cube 2 := by
    intro i
    fin_cases i <;> norm_num [x]
  apply (hausdorff_positivity _).mp _ k n h
  refine ⟨Measure.dirac x, inferInstance, fun m => ?_⟩
  rw [momentOf, setIntegral_dirac, ite_eq_left hx]
  by_cases hm : m 0 = 0 <;> simp [monomial, Fin.prod_univ_two, x, hm]

-- The moments `1, 0, 0, …` of the point mass at zero have nonnegative backward differences,
-- so the reverse direction produces a representing measure.
example : IsPositiveMomentConfiguration
    (fun m : Fin 1 → ℕ => if m 0 = 0 then (1 : ℝ) else 0) := by
  refine (hausdorff_positivity _).mpr fun k n hkn => ?_
  simp only [diff]
  refine Finset.sum_nonneg fun j hj => ?_
  have hjk : j 0 ≤ k 0 := Finset.mem_Iic.mp hj 0
  have hkn0 : k 0 ≤ n 0 := hkn 0
  by_cases h : (n - j) 0 = 0
  · -- Only `j = k = n` meets the atom, and its sign is `+1`.
    have hk : k 0 - j 0 = 0 := by
      rw [Pi.sub_apply] at h
      omega
    rw [ite_eq_left h, Fin.sum_univ_one, hk, pow_zero, one_mul, mul_one]
    positivity
  · rw [ite_eq_right h, mul_zero]

example (c : ℝ) :
    IsPositiveMomentConfiguration (fun _ : Fin 0 → ℕ => c) ↔ 0 ≤ c := by
  rw [hausdorff_positivity]
  have hd (k n : Fin 0 → ℕ) : diff (fun _ => c) k n = c := by
    simp [diff, multiChoose, Pi.card_Iic]
  simp [hd]
