/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.PotentialHeatRegularity
import MathlibExt.Analysis.PDE.BurgersExponentialGrowth
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Real Set Filter Topology
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

private theorem exp_abs_growth : HasExpGrowth (fun y : ℝ => exp |y|) :=
  ⟨1, 1, by norm_num, by norm_num, fun y => by simp [abs_of_pos (exp_pos _)]⟩

example {ν T a b : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ T) (x : ℝ) :
    potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) (a+b) x =
      potentialHeatSolution ν (fun s y => sin (a+s+y))
        (potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) a) b x :=
  potentialHeatSolution_restart hν (by fun_prop) (Q := 1) (by norm_num)
    (fun s _ y => abs_sin_le_one _) (by fun_prop) exp_abs_growth ha hb hab x

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioc 0 T) (x : ℝ) :
    DifferentiableAt ℝ (potentialHeatSolution ν (fun s y => sin (s+y))
      (fun y => exp |y|) t) x :=
  (potentialHeatSolution_hasDerivAt_space_of_continuous hν (by fun_prop)
    (Q := 1) (by norm_num) (fun s _ y => abs_sin_le_one _)
    (by fun_prop) exp_abs_growth ht x).differentiableAt

example {ν T : ℝ} (hν : 0 < ν) :
    ContinuousOn (fun p : ℝ × ℝ => deriv
      (potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) p.1) p.2)
      (Ioc 0 T ×ˢ univ) :=
  potentialHeatSolution_deriv_continuousOn hν (by fun_prop) (Q := 1) (by norm_num)
    (fun s _ y => abs_sin_le_one _) (by fun_prop) exp_abs_growth

example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hgg : HasExpGrowth g) (hgd : HasExpGrowth (deriv g)) :
    ContinuousOn (fun p : ℝ × ℝ => deriv
      (potentialHeatSolution ν (fun s y => sin (s+y)) g p.1) p.2) (Icc 0 T ×ˢ univ) :=
  potentialHeatSolution_deriv_continuousOn_of_contDiff hν hT (by fun_prop)
    (Q := 1) (by norm_num) (fun s _ y => abs_sin_le_one _) hg hgg hgd

example {ν T a : ℝ} (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => deriv (potentialHeatSolution ν (fun t y => sin (t+y))
        (fun y => exp |y|) (a+s)) x) (T-a) :=
  potentialHeatSolution_deriv_hasExpGrowthOnStrip hν (by fun_prop) (Q := 1) (by norm_num)
    (fun s _ y => abs_sin_le_one _) (by fun_prop) exp_abs_growth ha haT

-- The potential has a time cusp; neither potential differentiability nor initial C1
-- regularity is necessary for positive-time spatial smoothing.
private theorem rough_bound (T s : ℝ) (_ : s ∈ Icc 0 T) (y : ℝ) :
    abs (|sin s| * sin y) ≤ 1 := by
  rw [abs_mul, abs_abs]
  exact (mul_le_mul (abs_sin_le_one s) (abs_sin_le_one y) (abs_nonneg _) zero_le_one).trans
    (by norm_num)

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioc 0 T) (x : ℝ) :
    DifferentiableAt ℝ (potentialHeatSolution ν (fun s y => |sin s| * sin y)
      (fun y => exp |y|) t) x :=
  (potentialHeatSolution_hasDerivAt_space_of_continuous hν (by fun_prop)
    (Q := 1) (by norm_num) (rough_bound T) (by fun_prop) exp_abs_growth ht x).differentiableAt

example {ν T a : ℝ} (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => deriv (potentialHeatSolution ν (fun t y => |sin t| * sin y)
        (fun y => exp |y|) (a+s)) x) (T-a) :=
  potentialHeatSolution_deriv_hasExpGrowthOnStrip hν (by fun_prop) (Q := 1) (by norm_num)
    (rough_bound T) (by fun_prop) exp_abs_growth ha haT

-- A nonzero restart of a genuinely space-time dependent potential also permits ν=0.
example {T a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ T) (x : ℝ) :
    potentialHeatSolution 0 (fun s y => sin (s+y)) (fun y => exp |y|) (a+b) x =
      potentialHeatSolution 0 (fun s y => sin (a+s+y))
        (potentialHeatSolution 0 (fun s y => sin (s+y)) (fun y => exp |y|) a) b x :=
  potentialHeatSolution_restart le_rfl (by fun_prop) (Q := 1) (by norm_num)
    (fun s _ y => abs_sin_le_one _) (by fun_prop) exp_abs_growth ha hb hab x

-- Restarting at zero recovers the original initial datum, not a supplied substitute.
example {ν T b : ℝ} (hν : 0 ≤ ν) (hb : b ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) b x =
      heatSolution (fun y => exp |y|) (ν*b) x +
        heatDuhamel ν (fun s y => sin (s+y) *
          potentialHeatSolution ν (fun r z => sin (r+z)) (fun y => exp |y|) s y) b x := by
  have hi : potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) 0 =
      fun y => exp |y| := funext (potentialHeatSolution_initial ν _ _)
  simpa [hi] using potentialHeatSolution_restart_mild (q := fun s y => sin (s+y))
    (T := T) hν (by fun_prop) (Q := 1) (by norm_num)
    (fun s _ y => abs_sin_le_one _) (by fun_prop) exp_abs_growth (a := 0) le_rfl hb.1
    (by simpa using hb.2) x

private theorem cusp_velocity_bounded : ∃ M, ∀ x : ℝ, abs (|sin x|) ≤ M :=
  ⟨1,fun x => by simpa only [abs_abs] using abs_sin_le_one x⟩

-- A primitive of |sin x| gives a C1 heat profile without a C2 assumption.
example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (x₀ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (potentialHeatSolution ν
      (fun s y => |sin s| * sin y) (ColeHopf.initialHeatProfile ν (fun y => |sin y|) x₀) p.1) p.2)
      (Icc 0 T ×ˢ univ) :=
  potentialHeatSolution_deriv_continuousOn_of_contDiff hν hT (by fun_prop) (by norm_num)
    (rough_bound T) (ColeHopf.initialHeatProfile_contDiff (by fun_prop) ν x₀)
    (ColeHopf.initialHeatProfile_hasExpGrowth cusp_velocity_bounded hν x₀)
    (ColeHopf.initialHeatProfile_deriv_hasExpGrowth (by fun_prop) cusp_velocity_bounded hν x₀)

example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (x₀ : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun t x => deriv (potentialHeatSolution ν (fun s y => |sin s| * sin y)
        (ColeHopf.initialHeatProfile ν (fun y => |sin y|) x₀) t) x) T :=
  potentialHeatSolution_deriv_hasExpGrowthOnStrip_of_contDiff hν hT (by fun_prop) (by norm_num)
    (rough_bound T) (ColeHopf.initialHeatProfile_contDiff (by fun_prop) ν x₀)
    (ColeHopf.initialHeatProfile_hasExpGrowth cusp_velocity_bounded hν x₀)
    (ColeHopf.initialHeatProfile_deriv_hasExpGrowth (by fun_prop) cusp_velocity_bounded hν x₀)

-- Joint initial derivative recovery has the coefficient required by Cole-Hopf.
example {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (x₀ x : ℝ) :
    Tendsto (fun p : ℝ × ℝ => deriv (potentialHeatSolution ν (fun s y => |sin s| * sin y)
      (ColeHopf.initialHeatProfile ν (fun y => |sin y|) x₀) p.1) p.2)
      (𝓝[Icc 0 T ×ˢ univ] (0,x))
      (𝓝 (-|sin x| / (2*ν) * ColeHopf.initialHeatProfile ν (fun y => |sin y|) x₀ x)) := by
  have h := potentialHeatSolution_deriv_tendsto_initial hν hT (by fun_prop) (by norm_num)
    (rough_bound T) (ColeHopf.initialHeatProfile_contDiff (by fun_prop) ν x₀)
    (ColeHopf.initialHeatProfile_hasExpGrowth cusp_velocity_bounded hν x₀)
    (ColeHopf.initialHeatProfile_deriv_hasExpGrowth (by fun_prop) cusp_velocity_bounded hν x₀) x
  simpa only [(ColeHopf.initialHeatProfile_hasDerivAt
    (u₀ := fun y => |sin y|) (by fun_prop) ν x₀ x).deriv] using h

-- The positive lower endpoint may equal the terminal time.
example {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => deriv (potentialHeatSolution ν (fun t y => sin (t+y))
        (fun y => exp |y|) (T+s)) x) 0 := by
  simpa only [sub_self] using potentialHeatSolution_deriv_hasExpGrowthOnStrip hν
    (T := T) (by fun_prop) (Q := 1) (by norm_num) (fun s _ y => abs_sin_le_one _)
    (by fun_prop) exp_abs_growth hT le_rfl

-- The closed-strip C1 conclusion includes a zero horizon.
example {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (potentialHeatSolution ν
      (fun s y => |sin s| * sin y) (ColeHopf.initialHeatProfile ν (fun y => |sin y|) x₀) p.1) p.2)
      (Icc 0 0 ×ˢ univ) :=
  potentialHeatSolution_deriv_continuousOn_of_contDiff hν le_rfl (by fun_prop) (by norm_num)
    (rough_bound 0) (ColeHopf.initialHeatProfile_contDiff (by fun_prop) ν x₀)
    (ColeHopf.initialHeatProfile_hasExpGrowth cusp_velocity_bounded hν x₀)
    (ColeHopf.initialHeatProfile_deriv_hasExpGrowth (by fun_prop) cusp_velocity_bounded hν x₀)

-- A nonzero actual initial derivative checks the sign and the factor 2ν.
example : HasDerivAt (potentialHeatSolution 1 (fun s y => |sin s| * sin y)
    (ColeHopf.initialHeatProfile 1 (fun y => |sin y|) (π/2)) 0) (-1/2) (π/2) := by
  have h := potentialHeatSolution_hasDerivAt_space_of_contDiff (ν := 1) (T := 0)
    (by norm_num) (by fun_prop) (by norm_num) (rough_bound 0)
    (ColeHopf.initialHeatProfile_contDiff (by fun_prop) 1 (π/2))
    (ColeHopf.initialHeatProfile_hasExpGrowth cusp_velocity_bounded (by norm_num) (π/2))
    (ColeHopf.initialHeatProfile_deriv_hasExpGrowth (by fun_prop) cusp_velocity_bounded
      (by norm_num) (π/2)) (t := 0) ⟨le_rfl,le_rfl⟩ (π/2)
  have hd (f : ℝ → ℝ → ℝ) : heatDuhamel 1 f 0 = fun _ => 0 :=
    funext (heatDuhamel_zero_time 1 f)
  simpa [hd, (ColeHopf.initialHeatProfile_hasDerivAt (u₀ := fun y => |sin y|)
    (by fun_prop) 1 (π/2) (π/2)).deriv] using h
