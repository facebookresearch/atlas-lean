/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatDuhamelSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Real Set
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

-- Signed coefficients test interchange without positivity of the summands.
-- Unbounded data rule out relying on an unweighted bounded-functions theorem.
example (a : ℕ → ℝ) (ha : Summable (fun n => |a n|)) (t x : ℝ) :
    HasSum (fun n => heatSolution (fun y => a n * exp |y|) t x)
      (heatSolution (fun y => ∑' n, a n * exp |y|) t x) := by
  apply heatSolution_hasSum_of_exp_bound (A := fun n => |a n|) (c := 1)
    (fun n => (by fun_prop : Continuous (fun y : ℝ => a n * exp |y|)).aestronglyMeasurable)
    ha (by norm_num)
  intro n y
  simp [abs_mul, abs_of_pos (exp_pos _)]

-- The heat helper only requires measurability: a jump is permitted, including t<0.
example (a : ℕ → ℝ) (ha : Summable (fun n => |a n|)) (t x : ℝ) :
    HasSum (fun n => heatSolution (fun y => if y < 0 then a n else 0) t x)
      (heatSolution (fun y => ∑' n, if y < 0 then a n else 0) t x) := by
  apply heatSolution_hasSum_of_exp_bound (A := fun n => |a n|) (c := 0)
    (fun n => ((measurable_const.piecewise measurableSet_Iio measurable_const)
      : Measurable (fun y : ℝ => if y < 0 then a n else 0)).aestronglyMeasurable)
    ha le_rfl
  intro n y
  change |if y < 0 then a n else 0| ≤ |a n| * exp (0 * |y|)
  split_ifs <;> simp [abs_nonneg]

-- A genuine infinite series with a time-dependent cusp and exponential spatial growth.
example {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasSum (fun n : ℕ => heatDuhamel ν
      (fun s y => (1/2 : ℝ)^n * |sin s| * exp |y|) t x)
      (heatDuhamel ν (fun s y => ∑' n : ℕ, (1/2 : ℝ)^n * |sin s| * exp |y|) t x) := by
  apply heatDuhamel_hasSum_of_exp_bound (A := fun n : ℕ => (1/2 : ℝ)^n) (c := 1)
    (T := T) (fun n => by fun_prop) (fun n => by positivity)
    (summable_geometric_of_norm_lt_one (by norm_num)) (by norm_num) ?_ hν ht x
  intro n s hs y
  rw [abs_mul, abs_mul, abs_abs, abs_of_nonneg (by positivity : 0 ≤ (1/2 : ℝ)^n),
    abs_of_pos (exp_pos _), one_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by positivity) (abs_sin_le_one s)) (exp_pos _).le
