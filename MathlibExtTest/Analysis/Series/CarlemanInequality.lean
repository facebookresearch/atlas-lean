/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Series.CarlemanInequality
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for Carleman's inequality (sharp form, constant `e`)

* The geometric mean of a constant `1` sequence is `1`.
* The sequence `4, 1, 0, 0, …`: its first two geometric means are `4` and `2`,
  so the finite Carleman bound says `4 + 2 = 6 ≤ e * 5`, and the strengthened
  bound says `6 + 2 * 2 = 10 ≤ e * 5`.
* The geometric sequence `(1 / 2) ^ n`: the infinite Carleman bound gives
  `∑' n, G n ≤ e * 2`.
* `#print axioms` for the main theorems: standard triple only.
-/

namespace MathlibExtTest.Analysis.Series.CarlemanInequalityTests

open MetaMathlibExt

/-- The constant `1` sequence has geometric mean `1` at every step. -/
theorem geomMean_const_one (n : ℕ) : carlemanGeomMean (fun _ => (1 : ℝ)) n = 1 := by
  simp [carlemanGeomMean]

/-- The test sequence `4, 1, 0, 0, …`. -/
def testSeq : ℕ → ℝ := fun n => if n = 0 then 4 else if n = 1 then 1 else 0

/-- Every term of `testSeq` is nonnegative. -/
theorem testSeq_nonneg : ∀ n, 0 ≤ testSeq n := by
  intro n
  by_cases h0 : n = 0
  · subst h0; simp [testSeq]
  · by_cases h1 : n = 1
    · subst h1; simp [testSeq]
    · simp [testSeq, h0, h1]

/-- The first geometric mean of `testSeq` is `4`. -/
theorem geomMean_testSeq_zero : carlemanGeomMean testSeq 0 = 4 := by
  simp [carlemanGeomMean, testSeq]

/-- The second geometric mean of `testSeq` is `√(4 * 1) = 2`. -/
theorem geomMean_testSeq_one : carlemanGeomMean testSeq 1 = 2 := by
  unfold carlemanGeomMean
  have hprod : (∏ k ∈ Finset.range (1 + 1), testSeq k) = 4 := by
    rw [Finset.prod_range_succ, Finset.prod_range_one]
    simp [testSeq]
  rw [hprod]
  have h2 : ((((1 + 1 : ℕ) : ℝ))⁻¹) = (1 : ℝ) / 2 := by norm_num
  rw [h2]
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num [Real.rpow_natCast],
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]

/-- Finite Carleman bound on `testSeq`: `4 + 2 = 6 ≤ e * 5`. -/
theorem finite_example :
    (∑ n ∈ Finset.range 2, carlemanGeomMean testSeq n) ≤ Real.exp 1 * 5 := by
  have hsumG : (∑ n ∈ Finset.range 2, carlemanGeomMean testSeq n) = 6 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one,
      geomMean_testSeq_zero, geomMean_testSeq_one]
    norm_num
  have hsumA : (∑ n ∈ Finset.range 2, testSeq n) = 5 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [testSeq]; norm_num
  have h := carlemanGeomMean_sum_le testSeq_nonneg 2
  rw [hsumG, hsumA] at h
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have h2 := Real.add_one_le_exp (1 : ℝ)
    norm_num at h2
    exact h2
  linarith

/-- Strengthened finite Carleman bound on `testSeq`: `6 + 2 * 2 = 10 ≤ e * 5`. -/
theorem strengthened_example :
    (∑ n ∈ Finset.range 2, carlemanGeomMean testSeq n) +
      (2 : ℝ) * carlemanGeomMean testSeq 1 ≤ Real.exp 1 * 5 := by
  have hsumG : (∑ n ∈ Finset.range 2, carlemanGeomMean testSeq n) = 6 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one,
      geomMean_testSeq_zero, geomMean_testSeq_one]
    norm_num
  have hsumA : (∑ n ∈ Finset.range 2, testSeq n) = 5 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [testSeq]; norm_num
  have h := carlemanGeomMean_sum_add_mul_le testSeq_nonneg 1
  norm_num at h
  rw [hsumG, hsumA, geomMean_testSeq_one] at h
  rw [hsumG, geomMean_testSeq_one]
  linarith

/-- Infinite Carleman bound for the geometric sequence `(1 / 2) ^ n`, whose
series sums to `2`. -/
theorem infinite_geometric :
    ∑' n, carlemanGeomMean (fun n => (1 / 2 : ℝ) ^ n) n ≤ 2 * Real.exp 1 := by
  have hnn : ∀ n, 0 ≤ (1 / 2 : ℝ) ^ n := fun n => by positivity
  have hsumm : Summable (fun n => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h := (carleman_inequality hnn hsumm).2
  have htsum : ∑' n, (1 / 2 : ℝ) ^ n = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [htsum] at h
  linarith

#print axioms MetaMathlibExt.carleman_inequality
#print axioms MetaMathlibExt.carlemanGeomMean_sum_add_mul_le
#print axioms MetaMathlibExt.carlemanGeomMean_sum_le

end MathlibExtTest.Analysis.Series.CarlemanInequalityTests
