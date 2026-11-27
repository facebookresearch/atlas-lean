/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatDuhamelDerivatives
import MathlibExt.Analysis.PDE.BurgersExponentialGrowth
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Set Real
open MathlibExt.Analysis MathlibExt.Analysis.PDE
open MathlibExt.Analysis.PDE.HeatKernel

private theorem stationary_growth {f : ℝ → ℝ} (hf : HasExpGrowth f) (T : ℝ) :
    HeatWholeLine.HasExpGrowthOnStrip (fun _ => f) T := by
  obtain ⟨M, c, hM, hc, hb⟩ := hf
  exact ⟨M, c, hM, hc, fun _ _ => hb⟩

-- A merely bounded continuous initial velocity supplies C1 heat data; no second
-- initial derivative is required by the spatial Duhamel theorem.
private theorem profile_spatial_derivative {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (heatDuhamel ν (fun _ => ColeHopf.initialHeatProfile ν u₀ 0) t)
      (heatDuhamel ν (fun _ => deriv (ColeHopf.initialHeatProfile ν u₀ 0)) t x) x := by
  have hc := ColeHopf.initialHeatProfile_contDiff hu ν 0
  apply heatDuhamel_hasDerivAt_space (f := fun _ => ColeHopf.initialHeatProfile ν u₀ 0)
    (fx := fun _ => deriv (ColeHopf.initialHeatProfile ν u₀ 0)) hν.le
    (by simpa only [Function.uncurry_def, Function.comp_def] using
      (hc.continuous.comp continuous_snd).continuousOn)
    (by simpa only [Function.uncurry_def, Function.comp_def] using
      (hc.continuous_deriv_one.comp continuous_snd).continuousOn)
    (stationary_growth (ColeHopf.initialHeatProfile_hasExpGrowth hb hν 0) T)
    (stationary_growth (ColeHopf.initialHeatProfile_deriv_hasExpGrowth hu hb hν 0) T)
    (fun _ _ y => (hc.differentiable_one y).hasDerivAt) ht x

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (heatDuhamel ν
      (fun _ => ColeHopf.initialHeatProfile ν (fun y => |sin y|) 0) t)
      (heatDuhamel ν (fun _ => deriv
        (ColeHopf.initialHeatProfile ν (fun y => |sin y|) 0)) t x) x :=
  profile_spatial_derivative (by fun_prop)
    ⟨1, fun y => by simpa only [abs_abs] using abs_sin_le_one y⟩ hν ht x

example {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (heatDuhamel ν (fun _ y => exp y) t)
      (heatDuhamel ν (fun _ y => exp y) t x) x := by
  apply heatDuhamel_hasDerivAt_space hν (by fun_prop) (by fun_prop)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (fun _ _ y => Real.hasDerivAt_exp y) ht x

example {ν T t : ℝ} (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (deriv (heatDuhamel ν (fun _ y => exp y) t))
      (heatDuhamel ν (fun _ y => exp y) t x) x := by
  apply heatDuhamel_hasDerivAt_space_two hν (by fun_prop) (by fun_prop) (by fun_prop)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (fun _ _ y => Real.hasDerivAt_exp y) (fun _ _ y => Real.hasDerivAt_exp y) ht x

example {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (heatDuhamel ν (fun _ y => exp y) p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  apply heatDuhamel_deriv_continuousOn hν hT (by fun_prop) (by fun_prop)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (fun _ _ y => Real.hasDerivAt_exp y)

-- The time derivative is supplied by the source itself and the second spatial
-- derivative, even when no time derivative of the source is available.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => heatDuhamel ν (fun _ y => exp y) r x)
      (exp x + ν * heatDuhamel ν (fun _ y => exp y) t x) t := by
  apply heatDuhamel_hasDerivAt_time hν (by fun_prop) (by fun_prop) (by fun_prop)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) T)
    (fun _ _ y => Real.hasDerivAt_exp y) (fun _ _ y => Real.hasDerivAt_exp y) ht x

private noncomputable def cuspForcing (s x : ℝ) := |s - 1| * exp x

private theorem cusp_cont : ContinuousOn (Function.uncurry cuspForcing) (Icc 0 2 ×ˢ univ) := by
  unfold cuspForcing Function.uncurry
  fun_prop

private theorem cusp_growth : HeatWholeLine.HasExpGrowthOnStrip cuspForcing 2 := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro s hs x
  have hb : |s - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  calc
    |cuspForcing s x| = |s - 1| * exp x := by
      simp only [cuspForcing, abs_mul, abs_abs, abs_of_pos (exp_pos x)]
    _ ≤ 1 * exp |x| := mul_le_mul hb (exp_le_exp.mpr (le_abs_self x))
      (exp_pos x).le (by norm_num)
    _ = 1 * exp (1 * |x|) := by simp only [one_mul]

private theorem cusp_deriv (s x : ℝ) : HasDerivAt (cuspForcing s) (cuspForcing s x) x :=
  (Real.hasDerivAt_exp x).const_mul |s - 1|

-- The source is not time differentiable at t = 1. Its spatial derivatives
-- still meet the theorem's hypotheses, and its value at that time is zero.
example {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    HasDerivAt (fun r => heatDuhamel ν cuspForcing r x)
      (ν * heatDuhamel ν cuspForcing 1 x) 1 := by
  have hh := heatDuhamel_hasDerivAt_time hν cusp_cont cusp_cont cusp_cont
    cusp_growth cusp_growth cusp_growth (fun s _ => cusp_deriv s) (fun s _ => cusp_deriv s)
    (show (1 : ℝ) ∈ Ioo 0 2 by constructor <;> norm_num) x
  simpa [cuspForcing] using hh

example {ν t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioo 0 2) (x : ℝ) :
    deriv (fun r => heatDuhamel ν cuspForcing r x) t =
      ν * deriv (deriv (heatDuhamel ν cuspForcing t)) x + |t - 1| * exp x := by
  exact heatDuhamel_solves_heat hν cusp_cont cusp_cont cusp_cont
    cusp_growth cusp_growth cusp_growth (fun s _ => cusp_deriv s) (fun s _ => cusp_deriv s) ht x

example {ν : ℝ} (hν : 0 < ν) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun r => heatDuhamel ν cuspForcing r p.2) p.1)
      (Ioo 0 2 ×ˢ univ) :=
  heatDuhamel_time_deriv_continuousOn hν (by norm_num) cusp_cont cusp_cont cusp_cont
    cusp_growth cusp_growth cusp_growth (fun s _ => cusp_deriv s) (fun s _ => cusp_deriv s)

example {ν : ℝ} (hν : 0 ≤ ν) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (heatDuhamel ν cuspForcing p.1)) p.2)
      (Icc 0 2 ×ˢ univ) :=
  heatDuhamel_deriv_two_continuousOn hν (by norm_num) cusp_cont cusp_cont cusp_cont
    cusp_growth cusp_growth cusp_growth (fun s _ => cusp_deriv s) (fun s _ => cusp_deriv s)

-- The family continuity theorem includes zero and negative heat times,
-- independently of the time parameter indexing the forcing.
example : ContinuousOn
    (fun p : (ℝ × ℝ) × ℝ => heatSolution (cuspForcing p.1.1) p.1.2 p.2)
      ((Icc 0 2 ×ˢ univ) ×ˢ univ) :=
  heatSolution_family_continuousOn (by norm_num) cusp_cont cusp_growth

-- At zero viscosity the spatial formula still applies to the stationary extension.
example {t : ℝ} (ht : t ∈ Icc 0 2) (x : ℝ) :
    HasDerivAt (heatDuhamel 0 cuspForcing t) (heatDuhamel 0 cuspForcing t x) x :=
  heatDuhamel_hasDerivAt_space (by norm_num) cusp_cont cusp_cont cusp_growth cusp_growth
    (fun s _ => cusp_deriv s) ht x

-- A degenerate time strip is allowed by spatial differentiation.
example {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    HasDerivAt (heatDuhamel ν (fun _ y => exp y) 0) 0 x := by
  have hh := heatDuhamel_hasDerivAt_space hν
    (show ContinuousOn (Function.uncurry (fun _ y : ℝ => exp y)) (Icc 0 0 ×ˢ univ) by fun_prop)
    (by fun_prop) (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) 0)
    (stationary_growth (by simpa using HasExpGrowth.exp_linear 1) 0)
    (fun _ _ y => Real.hasDerivAt_exp y) (show (0 : ℝ) ∈ Icc 0 0 from ⟨le_rfl, le_rfl⟩) x
  simpa only [heatDuhamel_zero_time] using hh

-- The moving-endpoint source term is present even when both spatial derivatives vanish.
example {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    HasDerivAt (fun r => heatDuhamel ν (fun _ _ => (3 : ℝ)) r x) 3 1 := by
  have hg0 : HeatWholeLine.HasExpGrowthOnStrip (fun _ _ => (0 : ℝ)) 2 :=
    ⟨0, 0, by norm_num, by norm_num, by simp⟩
  have hg3 : HeatWholeLine.HasExpGrowthOnStrip (fun _ _ => (3 : ℝ)) 2 :=
    ⟨3, 0, by norm_num, by norm_num, by simp⟩
  have hh := heatDuhamel_hasDerivAt_time (f := fun _ _ => (3 : ℝ))
    (fx := fun _ _ => 0) (fxx := fun _ _ => 0) hν (by fun_prop) (by fun_prop) (by fun_prop)
    hg3 hg0 hg0 (fun _ _ y => hasDerivAt_const y 3) (fun _ _ y => hasDerivAt_const y 0)
    (show (1 : ℝ) ∈ Ioo 0 2 by constructor <;> norm_num) x
  simpa using hh
