/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.PotentialHeatSeries
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Real Set
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

example (ν : ℝ) (q : ℝ → ℝ → ℝ) (x : ℝ) :
    potentialHeatSolution ν q (fun y => exp |y|) 0 x = exp |x| :=
  potentialHeatSolution_initial ν q _ x

example (ν t x : ℝ) :
    potentialHeatSolution ν (fun _ _ => 0) (fun y => |sin y|) t x =
      heatSolution (fun y => |sin y|) (ν*t) x :=
  potentialHeatSolution_zero_potential ν _ t x

-- A negative nonzero potential tests the sign in the actual series.
example (ν t x : ℝ) :
    potentialHeatSolution ν (fun _ _ => -2) (fun _ => 3) t x = 3 * exp (-2*t) :=
  potentialHeatSolution_const ν (-2) 3 t x

-- The iterate formula tests the factorial denominator, including degree zero.
example (ν b a t x : ℝ) (n : ℕ) :
    potentialHeatIterate ν (fun _ _ => b) (fun _ => a) n t x =
      a * b^n * t^n / n.factorial :=
  potentialHeatIterate_const ν b a n t x

private theorem exp_abs_growth : HasExpGrowth (fun y : ℝ => exp |y|) :=
  ⟨1, 1, by norm_num, by norm_num, fun y => by simp [abs_of_pos (exp_pos _)]⟩

private theorem sin_bound (T s : ℝ) (_ : s ∈ Icc 0 T) (y : ℝ) : |sin (s+y)| ≤ 1 :=
  abs_sin_le_one _

-- The initial datum is unbounded and has a cusp, while the potential varies in
-- both variables. No differentiability of either input is assumed here.
example {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    Summable (fun n => ‖potentialHeatIterate ν (fun s y => sin (s+y))
      (fun y => exp |y|) n t x‖) :=
  summable_potentialHeatIterate hν (by fun_prop) (by norm_num) (sin_bound T)
    (by fun_prop) exp_abs_growth ht x

example {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ContinuousOn (Function.uncurry
      (potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|)))
      (Icc 0 T ×ˢ univ) :=
  potentialHeatSolution_continuousOn hν hT (by fun_prop) (by norm_num) (sin_bound T)
    (by fun_prop) exp_abs_growth

example {ν T : ℝ} (hν : 0 ≤ ν) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|)) T :=
  potentialHeatSolution_hasExpGrowthOnStrip hν (by fun_prop) (by norm_num) (sin_bound T)
    (by fun_prop) exp_abs_growth

example {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) t x =
      heatSolution (fun y => exp |y|) (ν*t) x +
        heatDuhamel ν (fun s y => sin (s+y) *
          potentialHeatSolution ν (fun r z => sin (r+z)) (fun z => exp |z|) s y) t x :=
  potentialHeatSolution_mild hν (by fun_prop) (by norm_num) (sin_bound T)
    (by fun_prop) exp_abs_growth ht x

-- Zero viscosity still has a meaningful Volterra equation, without a smoothing claim.
example {T t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution 0 (fun s y => sin (s+y)) (fun y => exp |y|) t x =
      exp |x| + heatDuhamel 0 (fun s y => sin (s+y) *
        potentialHeatSolution 0 (fun r z => sin (r+z)) (fun z => exp |z|) s y) t x := by
  simpa using potentialHeatSolution_mild (ν := 0) le_rfl (by fun_prop) (by norm_num)
    (sin_bound T) (by fun_prop) exp_abs_growth ht x

-- Initial continuity is joint within the closed strip, even when its horizon is zero.
example {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    ContinuousWithinAt (Function.uncurry
      (potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|)))
      (Icc 0 0 ×ˢ univ) (0,x) :=
  potentialHeatSolution_continuousOn hν le_rfl (by fun_prop) (by norm_num) (sin_bound 0)
    (by fun_prop) exp_abs_growth (0,x) ⟨⟨le_rfl, le_rfl⟩, mem_univ _⟩

-- Independently verify a nonzero mild solution by integrating exp, then use uniqueness.
-- Its chosen spatial growth exponent differs from the constant datum's exponent zero.
example {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    exp t = potentialHeatSolution ν (fun _ _ => 1) (fun _ => 1) t x := by
  have hug : MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s _ => exp s) T := by
    refine ⟨exp T, 2, (exp_pos _).le, by norm_num, fun s hs y => ?_⟩
    rw [abs_of_pos (exp_pos _)]
    exact (exp_le_exp.mpr hs.2).trans
      (le_mul_of_one_le_right (exp_pos _).le (one_le_exp (by positivity)))
  apply eq_potentialHeatSolution_of_mild (u := fun s _ => exp s)
    hν (by fun_prop) (Q := 1) (by norm_num) (by intros; norm_num)
    (by fun_prop) (g := fun _ => 1)
    ⟨1, 0, by norm_num, le_rfl, by intro y; simp⟩ (by fun_prop) hug ?_ ht x
  intro s hs y
  simp only [one_mul, heatSolution_const, heatDuhamel_time_only]
  rw [integral_exp]
  simp

-- The sharp bounded-data specialization has J=1 and no artificial Gaussian factor.
example {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    |potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => |sin y|) t x| ≤ exp t := by
  have hb (y : ℝ) : abs (|sin y|) ≤ (1 : ℝ) * exp (0 * |y|) := by
    simpa using abs_sin_le_one y
  simpa [integral_heatKernel one_pos] using abs_potentialHeatSolution_le hν (by fun_prop) (by norm_num) (sin_bound T)
    (by fun_prop) (by norm_num) le_rfl hb ht x
