/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HausdorffMoments

/-!
# Tests for the Hausdorff moment criteria

A point mass at a mixed corner has a nonconstant moment sequence. The difference of two
corner point masses gives moments of both signs. In dimension zero the sole moment can be
any nonnegative real number in the positive criterion and any real number in the signed one.
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

-- Two opposite signed corner atoms give moments of both signs.
example : HausdorffBounded
    (fun m : Fin 2 → ℕ => (if m 1 = 0 then 1 else 0) - (if m 0 = 0 then 1 else 0)) := by
  classical
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hx : x ∈ cube 2 := by
    intro i
    fin_cases i <;> norm_num [x]
  have hy : y ∈ cube 2 := by
    intro i
    fin_cases i <;> norm_num [y]
  apply (hausdorff_hildebrandt_schoenberg _).mp
  refine ⟨Measure.dirac x, Measure.dirac y, inferInstance, inferInstance, fun m => ?_⟩
  rw [momentOf, momentOf, setIntegral_dirac, setIntegral_dirac, ite_eq_left hx, ite_eq_left hy]
  by_cases h₀ : m 0 = 0 <;> by_cases h₁ : m 1 = 0 <;>
    simp [monomial, Fin.prod_univ_two, x, y, h₀, h₁]

-- The signed criterion has no positivity restriction on the sole moment in dimension zero.
example (c : ℝ) : IsMomentConfiguration (fun _ : Fin 0 → ℕ => c) := by
  apply (hausdorff_hildebrandt_schoenberg _).mpr
  refine ⟨|c|, fun n => ?_⟩
  have hd (k : Fin 0 → ℕ) : diff (fun _ => c) k n = c := by
    simp [diff, multiChoose, Pi.card_Iic]
  simp [hd, multiChoose, Pi.card_Iic]
