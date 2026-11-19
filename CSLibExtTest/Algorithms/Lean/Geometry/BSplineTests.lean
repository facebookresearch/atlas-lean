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
import CSLibExt.Algorithms.Lean.Geometry.BSpline

open Cslib.Algorithms.Lean.Geometry.BSpline

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
