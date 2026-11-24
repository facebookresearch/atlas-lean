/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.PotentialHeatGauge
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open Set Real MeasureTheory
open scoped ContDiff Interval
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

example {q : ℝ → ℝ → ℝ} {g r : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (hr : ContinuousOn r (Icc 0 T))
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν (fun s y => q s y + r s) g t x =
      exp (∫ s in 0..t, r s) * potentialHeatSolution ν q g t x :=
  potentialHeatSolution_add_time_potential hν hT hqs hqc hqb hg hgg hr ht x

private theorem zero_potential_data (T : ℝ) :
    (∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ))) ∧
    (∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) p.2)
      (Icc 0 T ×ˢ univ)) ∧
    (∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x : ℝ,
      |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x| ≤ M) :=
  ⟨fun _ _ => contDiff_const,fun k _ => by simp; fun_prop,
    fun k _ => ⟨0,fun _ _ _ => by simp⟩⟩

-- Exact positive exponential factor, signed nonintegrable initial data,
-- nonunit viscosity, and terminal time all occur in this concrete identity.
example (x : ℝ) : potentialHeatSolution 3 (fun _ _ => 2) (fun _ => -3) 1 x = -3*exp 2 := by
  obtain ⟨hs,hc,hb⟩ := zero_potential_data 1
  have hg : HasExpGrowth (fun _ : ℝ => (-3 : ℝ)) :=
    ⟨3,0,by norm_num,le_rfl,fun _ => by norm_num⟩
  have h := potentialHeatSolution_add_time_potential (q := fun _ _ => 0) (r := fun _ => 2)
    (g := fun _ => -3) (ν := 3) (by norm_num) (by norm_num) hs hc hb continuous_const hg
    continuousOn_const (t := 1) (by constructor <;> norm_num) x
  simpa only [zero_add,intervalIntegral.integral_const,sub_zero,smul_eq_mul,
    mul_one,one_mul,potentialHeatSolution_zero_potential,heatSolution_const,mul_comm] using h

-- A correction with a temporal corner only requires continuity.
example (t x : ℝ) (ht : t ∈ Icc 0 3) :
    potentialHeatSolution 3 (fun s _ => |s-1|) (fun _ => 2) t x =
      2*exp (∫ s in 0..t, |s-1|) := by
  obtain ⟨hs,hc,hb⟩ := zero_potential_data 3
  have hg : HasExpGrowth (fun _ : ℝ => (2 : ℝ)) :=
    ⟨2,0,by norm_num,le_rfl,fun _ => by norm_num⟩
  simpa [potentialHeatSolution_zero_potential,mul_comm] using
    potentialHeatSolution_add_time_potential (q := fun _ _ => 0) (r := fun s => |s-1|)
      (g := fun _ => 2) (ν := 3) (by norm_num) (by norm_num) hs hc hb continuous_const hg
      (by fun_prop) ht x

-- Exponential-growth data need not be bounded or integrable on the whole line.
example (t x : ℝ) (ht : t ∈ Icc 0 2) :
    potentialHeatSolution 3 (fun _ _ => -2) exp t x =
      exp (-2*t) * heatSolution exp (3*t) x := by
  obtain ⟨hs,hc,hb⟩ := zero_potential_data 2
  have hg : HasExpGrowth exp := ⟨1,1,by norm_num,by norm_num,fun y => by
    simpa only [abs_of_pos (exp_pos _),one_mul] using exp_le_exp.mpr (le_abs_self y)⟩
  simpa [potentialHeatSolution_zero_potential,mul_comm] using
    potentialHeatSolution_add_time_potential (q := fun _ _ => 0) (r := fun _ => -2)
      (g := exp) (ν := 3) (by norm_num) (by norm_num) hs hc hb continuous_exp hg
      continuousOn_const ht x

-- At zero horizon, no regularity of the correction outside {0} is required.
example (r : ℝ → ℝ) (x : ℝ) :
    potentialHeatSolution 3 (fun s _ => 0+r s) (fun _ => 1) 0 x =
      exp (∫ s in 0..0, r s) * potentialHeatSolution 3 (fun _ _ => 0) (fun _ => 1) 0 x := by
  obtain ⟨hs,hc,hb⟩ := zero_potential_data 0
  have hg : HasExpGrowth (fun _ : ℝ => (1 : ℝ)) :=
    ⟨1,0,by norm_num,le_rfl,fun _ => by norm_num⟩
  have hr : ContinuousOn r (Icc 0 0) := by simp
  exact potentialHeatSolution_add_time_potential (q := fun _ _ => 0) (r := r)
    (g := fun _ => 1) (ν := 3) (by norm_num) le_rfl hs hc hb continuous_const hg hr
    (t := 0) ⟨le_rfl,le_rfl⟩ x
