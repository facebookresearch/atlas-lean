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

A point mass at a mixed corner has a nonconstant moment sequence. In dimension zero
the sole moment can be any nonnegative real number.
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

example (c : ℝ) :
    IsPositiveMomentConfiguration (fun _ : Fin 0 → ℕ => c) ↔ 0 ≤ c := by
  rw [hausdorff_positivity]
  have hd (k n : Fin 0 → ℕ) : diff (fun _ => c) k n = c := by
    simp [diff, multiChoose, Pi.card_Iic]
  simp [hd]
