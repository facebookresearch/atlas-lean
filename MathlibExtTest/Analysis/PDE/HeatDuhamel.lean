/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatDuhamel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Topology
open MathlibExt.Analysis.PDE.HeatKernel
open MathlibExt.Analysis.PDE

example (ν x : ℝ) : heatDuhamel ν (fun t y => t + y ^ 2) 0 x = 0 := by simp

example (ν t x : ℝ) : heatDuhamel ν (fun _ _ => (3 : ℝ)) t x = 3 * t := by
  rw [heatDuhamel_const]
  ring

example (ν t x : ℝ) :
    heatDuhamel ν (fun s _ => |s - 1|) t x = ∫ s in 0..t, |s - 1| :=
  heatDuhamel_time_only ν (fun s => |s - 1|) t x

example (ν t x : ℝ) (ht : 0 ≤ t) :
    0 ≤ heatDuhamel ν (fun s y => (s - y) ^ 2) t x :=
  heatDuhamel_nonneg ν (fun _ _ _ => sq_nonneg _) ht x

private theorem exp_source_growth (T : ℝ) :
    HeatWholeLine.HasExpGrowthOnStrip (fun s x => Real.exp (s + x)) T := by
  refine ⟨Real.exp T, 1, (Real.exp_pos _).le, zero_le_one, fun s hs x => ?_⟩
  rw [abs_of_pos (Real.exp_pos _), one_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (add_le_add hs.2 (le_abs_self _))

example (ν T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ =>
      heatDuhamel ν (fun s x => Real.exp (s + x)) p.1 p.2) (Icc 0 T ×ˢ univ) :=
  heatDuhamel_continuousOn hT (by fun_prop) (exp_source_growth T) ν

example (ν T t x : ℝ) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun s => heatSolution (fun y => Real.exp (s + y))
      (ν * (t - s)) x) volume 0 t :=
  intervalIntegrable_heatDuhamel (by fun_prop) (exp_source_growth T) ν ht x

-- A quantitative bound must be available for genuinely unbounded spatial data.
example (ν T t x : ℝ) (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) :
    |heatDuhamel ν (fun s y => Real.exp (s + y)) t x| ≤
      t * Real.exp T * (∫ y : ℝ, heatKernel ℝ 1 y *
        Real.exp (Real.sqrt (ν * T) * |y|)) * Real.exp |x| := by
  have hb (s : ℝ) (hs : s ∈ Icc 0 T) (y : ℝ) :
      |Real.exp (s + y)| ≤ Real.exp T * Real.exp (1 * |y|) := by
    rw [one_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add hs.2 (le_abs_self _))
  simpa only [one_mul] using
    abs_heatDuhamel_le (by fun_prop) (Real.exp_pos T).le zero_le_one hb hν ht x

example (ν T : ℝ) (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    HeatWholeLine.HasExpGrowthOnStrip
      (heatDuhamel ν (fun s y => Real.exp (s + y))) T :=
  heatDuhamel_hasExpGrowthOnStrip (by fun_prop) (exp_source_growth T) hν hT

example (ν T t x : ℝ) (ht : t ∈ Icc 0 T) :
    heatDuhamel ν (fun s y => Real.exp (s + y) + Real.exp (s + y)) t x =
      2 * heatDuhamel ν (fun s y => Real.exp (s + y)) t x := by
  rw [heatDuhamel_add (by fun_prop) (by fun_prop)
    (exp_source_growth T) (exp_source_growth T) ν ht x]
  ring

example (ν T t x : ℝ) (ht : t ∈ Icc 0 T) :
    heatDuhamel ν (fun _ _ => (0 : ℝ)) t x ≤
      heatDuhamel ν (fun s y => Real.exp (s + y)) t x := by
  apply heatDuhamel_mono (by fun_prop) (by fun_prop)
    (HeatWholeLine.HasExpGrowthOnStrip.of_bounded ⟨0, by simp⟩)
    (exp_source_growth T) (fun _ _ _ => (Real.exp_pos _).le) ν ht x

-- A time-dependent source exercises the physical integration interval.
example (ν t x : ℝ) : heatDuhamel ν (fun s _ => s) t x = t ^ 2 / 2 := by
  rw [heatDuhamel_time_only, integral_id]
  simp

-- The initial trace is joint in time and space, not just along a fixed point.
example (ν T x : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun p : ℝ × ℝ => heatDuhamel ν (fun s y => Real.exp (s + y)) p.1 p.2)
      (𝓝[Icc 0 T ×ˢ univ] (0, x)) (𝓝 0) := by
  have h := (heatDuhamel_continuousOn hT (by fun_prop) (exp_source_growth T) ν)
    (0, x) ⟨⟨le_rfl, hT⟩, mem_univ _⟩
  simpa only [ContinuousWithinAt, Function.uncurry_def, heatDuhamel_zero_time] using h

-- The assumptions permit discontinuities outside the closed strip.
example (ν : ℝ) : ContinuousOn
    (Function.uncurry (heatDuhamel ν
      (fun s y => if s ∈ Icc (0 : ℝ) 1 then Real.exp y else 0)))
    (Icc 0 1 ×ˢ univ) := by
  apply heatDuhamel_continuousOn zero_le_one
  · apply (Real.continuous_exp.comp continuous_snd).continuousOn.congr
    intro p hp
    simp only [Function.uncurry_def, ite_eq_left hp.1, Function.comp_apply]
  · refine ⟨1, 1, zero_le_one, zero_le_one, fun s hs y => ?_⟩
    simp only [ite_eq_left hs, abs_of_pos (Real.exp_pos _), one_mul]
    exact Real.exp_le_exp.mpr (le_abs_self _)

-- Zero viscosity is the stationary heat extension, not a division-by-zero case.
example (f : ℝ → ℝ → ℝ) (t x : ℝ) :
    heatDuhamel 0 f t x = ∫ s in 0..t, f s x := by
  simp [heatDuhamel, heatSolution_of_nonpos]
