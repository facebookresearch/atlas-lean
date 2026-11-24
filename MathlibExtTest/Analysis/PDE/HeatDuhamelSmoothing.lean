/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatDuhamelSmoothing
import MathlibExt.Analysis.PDE.HeatDuhamelDerivatives
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel
open MathlibExt.Analysis.PDE.HeatWholeLine

private theorem cusp_growth (T : ℝ) :
    HasExpGrowthOnStrip (fun _ y => |sin y|) T := by
  refine ⟨1,0, by norm_num, le_rfl, fun _ _ y => ?_⟩
  simpa only [abs_abs,zero_mul,exp_zero,mul_one] using abs_sin_le_one y

-- No spatial derivative exists at all cusps of this forcing.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    DifferentiableAt ℝ (heatDuhamel ν (fun _ y => |sin y|) t) x :=
  (heatDuhamel_hasDerivAt_space_of_continuous hν (by fun_prop) (cusp_growth T) ht x).differentiableAt

example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (heatDuhamel ν (fun _ y => |sin y|) p.1) p.2)
      (Icc 0 T ×ˢ univ) :=
  heatDuhamel_deriv_continuousOn_of_continuous hν hT (by fun_prop) (cusp_growth T)

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    |deriv (heatDuhamel ν (fun _ y => |sin y|) t) x| ≤
      (sqrt t / sqrt ν) * (∫ y : ℝ, |y| * heatKernel ℝ 1 y) := by
  simpa using abs_heatDuhamel_deriv_le (by fun_prop) (M := 1) (c := 0)
    (by norm_num) le_rfl
    (fun _ _ y => by simpa only [abs_abs,zero_mul,exp_zero,mul_one] using abs_sin_le_one y)
    hν ht x

-- Closed-strip continuity includes the actual spatial derivative at time zero.
example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (x : ℝ) :
    ContinuousWithinAt (fun p : ℝ × ℝ => deriv (heatDuhamel ν (fun _ y => |sin y|) p.1) p.2)
      (Icc 0 T ×ˢ univ) (0,x) :=
  heatDuhamel_deriv_continuousOn_of_continuous hν hT (by fun_prop) (cusp_growth T)
    (0,x) ⟨⟨le_rfl,hT⟩, mem_univ _⟩

-- A degenerate strip still supplies a spatial derivative, without a time-neighborhood claim.
example {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    HasDerivAt (heatDuhamel ν (fun _ y => |sin y|) 0) 0 x := by
  simpa only [sqrt_zero,zero_div,neg_zero,zero_mul] using
    heatDuhamel_hasDerivAt_space_of_continuous hν (T := 0) (by fun_prop)
      (cusp_growth 0) ⟨le_rfl,le_rfl⟩ x

-- Unbounded spatial data and a time cusp are permitted simultaneously.
private theorem rough_growth (T : ℝ) :
    HasExpGrowthOnStrip (fun s y => |s-1| * exp |y|) T := by
  refine ⟨|T|+1,1, by positivity,by norm_num,fun s hs y => ?_⟩
  rw [abs_mul,abs_abs,abs_of_pos (exp_pos _),one_mul]
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  calc
    |s-1| ≤ |s|+1 := by simpa using abs_sub s 1
    _ ≤ |T|+1 := add_le_add
      (show |s| ≤ |T| by rw [abs_of_nonneg hs.1]; exact hs.2.trans (le_abs_self T)) le_rfl

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (heatDuhamel ν (fun s y => |s-1| * exp |y|) t)
      (-(sqrt t / sqrt ν) * ∫ r in (0 : ℝ)..1, ∫ y : ℝ, y * heatKernel ℝ 1 y *
        (|t * (1 - r ^ 2)-1| * exp |x - (sqrt (ν * t) * r) * y|)) x :=
  heatDuhamel_hasDerivAt_space_of_continuous hν (by fun_prop) (rough_growth T) ht x

example {ν T : ℝ} (hν : 0 < ν) :
    HasExpGrowthOnStrip (fun t x => deriv (heatDuhamel ν (fun s y => |s-1| * exp |y|) t) x) T :=
  heatDuhamel_deriv_hasExpGrowthOnStrip hν (by fun_prop) (rough_growth T)

-- A nonzero exact derivative checks the sign and viscosity normalization against
-- derivative transfer for linear forcing, whose Duhamel derivative is t.
private theorem linear_growth (T : ℝ) : HasExpGrowthOnStrip (fun _ y : ℝ => y) T := by
  refine ⟨1,1, by norm_num,by norm_num,fun _ _ y => ?_⟩
  simpa only [one_mul] using
    (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp |y|)

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    -(sqrt t / sqrt ν) * (∫ r in (0 : ℝ)..1, ∫ y : ℝ,
      y * heatKernel ℝ 1 y * (x - (sqrt (ν * t) * r) * y)) = t := by
  have hnew := heatDuhamel_hasDerivAt_space_of_continuous hν (f := fun _ y : ℝ => y)
    (by fun_prop) (linear_growth T) ht x
  have hold := heatDuhamel_hasDerivAt_space (fx := fun _ _ => 1) hν.le
    (by fun_prop) (by fun_prop) (linear_growth T)
    (show HasExpGrowthOnStrip (fun _ _ => 1) T from
      ⟨1,0, by norm_num, le_rfl,by intro s hs y; simp⟩)
    (fun _ _ y => hasDerivAt_id y) ht x
  simpa only [heatDuhamel_const,mul_one] using hnew.unique hold

-- The square-root representation also includes zero viscosity; smoothing does not claim it.
example {T t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    heatDuhamel 0 (fun _ y => |sin y|) t x =
      2 * t*∫ r in (0 : ℝ)..1, r * |sin x| := by
  simpa using heatDuhamel_sqrt_rescaled (by fun_prop) (cusp_growth T) 0 ht x
