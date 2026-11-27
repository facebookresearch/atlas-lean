/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Basic.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.Interpolation.BSpline

open MathlibExt.Interpolation.BSpline

/-- T1a. Uniform knots, degree 2, at 1/2. -/
theorem T1a : B (fun i => (i : ℝ)) 0 2 (1 / 2) = 1 / 8 := by
  simp [B]
  norm_num

/-- T1b. Uniform knots, degree 2, at 3/2. -/
theorem T1b : B (fun i => (i : ℝ)) 0 2 (3 / 2) = 3 / 4 := by
  simp [B]
  norm_num

/-- T2. Partition of unity at m = 5, k = 2, x = 5/2. -/
theorem T2 :
    ∑ i ∈ Finset.range 3, B (fun i => (i : ℝ)) i 2 (5 / 2) = 1 := by
  simp [Finset.sum_range_succ, B]
  norm_num

/-- T3. Double knot: degree-0 basis vanishes at the repeated span. -/
theorem T3 :
    B (fun i => if i = 0 then 0 else if i = 1 then 1 else (i : ℝ) - 1) 1 0 = 0 := by
  apply B_zero_of_repeated
  simp
  norm_num

/-- T4. Double knot `0, 1, 1, 2`, degree 1: the left coefficient of the
recursion has denominator `t 2 - t 1 = 0`, and the half-open span `[t 2, t 3)`
gives `B t 1 1 1 = 1`. -/
theorem T4 :
    B (fun i => if i = 0 then 0 else if i = 1 then 1 else (i : ℝ) - 1) 1 1 1 = 1 := by
  norm_num [B]

/-- T5. Same knots: the right coefficient of `B t 0 1` has denominator
`t 2 - t 1 = 0`, so at `1/2` only the left term contributes. -/
theorem T5 :
    B (fun i => if i = 0 then 0 else if i = 1 then 1 else (i : ℝ) - 1) 0 1 (1 / 2)
      = 1 / 2 := by
  norm_num [B]

/-- T6. Same knots: `B t 0 1` is `0` at the double knot, where `B t 1 1` is `1`
(T4); a degree-1 basis function jumps at a knot of multiplicity 2. -/
theorem T6 :
    B (fun i => if i = 0 then 0 else if i = 1 then 1 else (i : ℝ) - 1) 0 1 1 = 0 := by
  norm_num [B]

/-- T7. Same knots: partition of unity at the double knot `x = t 1 = t 2 = 1`
(m = 4, k = 1). -/
theorem T7 :
    ∑ i ∈ Finset.range 3,
      B (fun i => if i = 0 then 0 else if i = 1 then 1 else (i : ℝ) - 1) i 1 1 = 1 := by
  norm_num [Finset.sum_range_succ, B]

/-- T8. Triple knots `0, 0, 0, 1, 1, 1`, degree 2: the basis is the Bernstein
basis `(1 - x)^2, 2x(1 - x), x^2`, here at `x = 1/4`; both coefficients meet
zero denominators in the recursion. -/
theorem T8 :
    B (fun i => if i ≤ 2 then 0 else 1) 0 2 (1 / 4) = 9 / 16 ∧
      B (fun i => if i ≤ 2 then 0 else 1) 1 2 (1 / 4) = 3 / 8 ∧
      B (fun i => if i ≤ 2 then 0 else 1) 2 2 (1 / 4) = 1 / 16 := by
  norm_num [B]

/-- T9. `B_partition_of_unity` applies to the double-knot sequence of T4:
on `[1, 2)` the three degree-1 basis functions sum to `1`. -/
theorem T9 (x : ℝ) (h1 : 1 ≤ x) (h2 : x < 2) :
    ∑ i ∈ Finset.range 3,
      B (fun i => if i = 0 then 0 else if i = 1 then 1 else (i : ℝ) - 1) i 1 x = 1 := by
  refine B_partition_of_unity (m := 4) ?_ (by norm_num) (by norm_num [h1]) (by norm_num [h2])
  refine monotone_nat_of_le_succ fun n => ?_
  rcases n with _ | _ | n <;> norm_num
