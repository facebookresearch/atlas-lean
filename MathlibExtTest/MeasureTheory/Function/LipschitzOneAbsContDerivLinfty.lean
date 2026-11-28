/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LipschitzOneAbsContDerivLinfty
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open MathlibExt.MeasureTheory.LipschitzOneAbsContDerivLinftyWanted
open scoped ENNReal

-- The absolute-value function has a corner inside the interval.
example : AbsolutelyContinuousOnInterval (fun x : ℝ => |x|) (-1) 1 ∧
    eLpNorm (fun x : ℝ => deriv (fun y : ℝ => |y|) x) ∞
      (volume.restrict (Icc (-1 : ℝ) 1)) < ∞ := by
  have h : LipschitzWith 1 (fun x : ℝ => |x|) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
  exact absolutelyContinuousOnInterval_and_eLpNorm_deriv_lt_top_of_lipschitzOnWith
    (by norm_num) h.lipschitzOnWith

-- On a singleton interval no regularity away from the singleton is needed.
example (f : ℝ → ℝ) : AbsolutelyContinuousOnInterval f 0 0 ∧
    eLpNorm (fun x => deriv f x) ∞ (volume.restrict (Icc (0 : ℝ) 0)) < ∞ := by
  apply absolutelyContinuousOnInterval_and_eLpNorm_deriv_lt_top_of_lipschitzOnWith le_rfl
  intro x hx y hy
  rw [Icc_self, mem_singleton_iff] at hx hy
  subst x
  subst y
  simp
