/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.PotentialHeatPositivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Real
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

-- Positive rough data tending to zero at infinity: no uniform lower bound is assumed.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    0 < potentialHeatSolution ν (fun _ _ => -2) (fun x => exp (-|x|)) t x := by
  apply potentialHeatSolution_pos hν (fun _ _ => contDiff_const)
    (fun k _ => by simp only [iteratedDeriv_const]; split_ifs <;> fun_prop)
    (fun k _ => ⟨2, fun _ _ _ => by simp only [iteratedDeriv_const]; split_ifs <;> norm_num⟩)
    (by fun_prop)
    ⟨1,0,by norm_num,le_rfl,fun y => by
      simp only [abs_of_pos (exp_pos _),zero_mul,exp_zero,mul_one]
      exact exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))⟩
    (fun y => exp_pos _) ht x

private theorem trig_jet_bound (k : ℕ) :
    (∀ x : ℝ, |iteratedDeriv k sin x| ≤ 1) ∧ (∀ x : ℝ, |iteratedDeriv k cos x| ≤ 1) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using And.intro abs_sin_le_one abs_cos_le_one
  | succ k ih =>
    constructor
    · simpa only [iteratedDeriv_add_one_sin] using ih.2
    · simpa only [iteratedDeriv_add_one_cos, Pi.neg_apply, abs_neg] using ih.1

private theorem sine_cont (k : ℕ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (fun y => sin (p.1+y)) p.2)
      (Icc 0 T ×ˢ univ) := by
  simp_rw [iteratedDeriv_comp_const_add]
  exact ((differentiable_iteratedDeriv_sin k).continuous.comp (by fun_prop)).continuousOn

private theorem sine_bound (k : ℕ) (T : ℝ) :
    ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (fun y => sin (s+y)) x| ≤ M :=
  ⟨1, fun s _ x => by rw [iteratedDeriv_comp_const_add]; exact (trig_jet_bound k).1 _⟩

private theorem exp_abs_growth : HasExpGrowth (fun x : ℝ => exp |x|) :=
  ⟨1,1,by norm_num,by norm_num,fun x => by simp [abs_of_pos (exp_pos _)]⟩

-- A sign-changing space-time potential with unbounded, non-C1 initial data.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    exp (-t)*heatSolution (fun x => exp |x|) (ν*t) x ≤
        potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => exp |x|) t x ∧
      potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => exp |x|) t x ≤
        exp t*heatSolution (fun x => exp |x|) (ν*t) x := by
  simpa only [neg_mul,one_mul] using
    potentialHeatSolution_heat_bounds (q := fun s y => sin (s+y)) (Q := 1)
      hν (fun _ _ => by fun_prop) (fun k _ => sine_cont k T)
      (fun k _ => sine_bound k T) (by norm_num) (fun _ _ _ => abs_sin_le_one _)
      (by fun_prop) exp_abs_growth (fun _ => (exp_pos _).le) ht x

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    0 < potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => exp |x|) t x :=
  potentialHeatSolution_pos hν (fun _ _ => by fun_prop) (fun k _ => sine_cont k T)
    (fun k _ => sine_bound k T) (by fun_prop) exp_abs_growth (fun _ => exp_pos _) ht x

-- The theorem includes nonnegative data that vanish at some spatial points.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    0 ≤ potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => sin x ^ 2) t x := by
  apply potentialHeatSolution_nonneg hν (fun _ _ => by fun_prop)
    (fun k _ => sine_cont k T) (fun k _ => sine_bound k T) (by fun_prop)
    (HasExpGrowth.of_bounded ⟨1, fun x => ?_⟩) (fun _ => sq_nonneg _) ht x
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (abs_sin_le_one x)

-- The positive-time conclusion is not used to falsely claim positive initial data at a zero.
example (ν : ℝ) :
    potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => sin x ^ 2) 0 0 = 0 := by
  simp

-- Zero potential collapses the two quantitative bounds to the same free heat value.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    heatSolution (fun x => exp |x|) (ν*t) x ≤
        potentialHeatSolution ν (fun _ _ => 0) (fun x => exp |x|) t x ∧
      potentialHeatSolution ν (fun _ _ => 0) (fun x => exp |x|) t x ≤
        heatSolution (fun x => exp |x|) (ν*t) x := by
  simpa only [neg_zero,zero_mul,exp_zero,one_mul] using
    potentialHeatSolution_heat_bounds (q := fun _ _ => 0) (Q := 0) hν
      (fun _ _ => contDiff_const)
      (fun k _ => by simp only [iteratedDeriv_const]; split_ifs <;> fun_prop)
      (fun k _ => ⟨0, fun _ _ _ => by simp⟩)
      le_rfl (by simp) (by fun_prop) exp_abs_growth (fun _ => (exp_pos _).le) ht x

-- Constant positive and negative potentials attain the respective sharp bounds.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    exp (-2*t) ≤ potentialHeatSolution ν (fun _ _ => 2) (fun _ => 1) t x ∧
      potentialHeatSolution ν (fun _ _ => 2) (fun _ => 1) t x = exp (2*t) := by
  have hb := potentialHeatSolution_heat_bounds (q := fun _ _ => 2) (g := fun _ => 1)
    (Q := 2) hν (fun _ _ => contDiff_const)
    (fun k _ => by simp only [iteratedDeriv_const]; split_ifs <;> fun_prop)
    (fun k _ => ⟨2, fun _ _ _ => by simp only [iteratedDeriv_const]; split_ifs <;> norm_num⟩)
    (by norm_num) (by intros; norm_num) continuous_const
    (HasExpGrowth.of_bounded ⟨1, by simp⟩) (by simp) ht x
  exact ⟨by simpa only [heatSolution_const,mul_one] using hb.1, by simp⟩

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν (fun _ _ => -2) (fun _ => 1) t x = exp (-2*t) ∧
      potentialHeatSolution ν (fun _ _ => -2) (fun _ => 1) t x ≤ exp (2*t) := by
  have hb := potentialHeatSolution_heat_bounds (q := fun _ _ => -2) (g := fun _ => 1)
    (Q := 2) hν (fun _ _ => contDiff_const)
    (fun k _ => by simp only [iteratedDeriv_const]; split_ifs <;> fun_prop)
    (fun k _ => ⟨2, fun _ _ _ => by simp only [iteratedDeriv_const]; split_ifs <;> norm_num⟩)
    (by norm_num) (by intros; norm_num) continuous_const
    (HasExpGrowth.of_bounded ⟨1, by simp⟩) (by simp) ht x
  exact ⟨by simp, by simpa only [heatSolution_const,mul_one] using hb.2⟩

private theorem id_growth : HasExpGrowth (fun x : ℝ => x) :=
  ⟨1,1,by norm_num,by norm_num,fun x => by simp only [one_mul]; linarith [add_one_le_exp |x|]⟩

private theorem id_add_exp_growth : HasExpGrowth (fun x : ℝ => x+exp (2*x)) := by
  refine ⟨2,2,by norm_num,by norm_num,fun x => ?_⟩
  have hx : |x| ≤ exp (2*|x|) :=
    (by linarith [add_one_le_exp |x|] : |x| ≤ exp |x|).trans
      (exp_le_exp.mpr (by linarith [abs_nonneg x]))
  have he : exp (2*x) ≤ exp (2*|x|) := exp_le_exp.mpr (by linarith [le_abs_self x])
  have ha := abs_add_le x (exp (2*x))
  rw [abs_of_pos (exp_pos _)] at ha
  linarith

-- Ordered, sign-changing unbounded data with different growth rates.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => x) t x ≤
      potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => x+exp (2*x)) t x :=
  potentialHeatSolution_mono_initial hν (fun _ _ => by fun_prop)
    (fun k _ => sine_cont k T) (fun k _ => sine_bound k T)
    continuous_id id_growth (by fun_prop) id_add_exp_growth
    (fun y => le_add_of_nonneg_right (exp_pos _).le) ht x

-- A degenerate strip still recovers pointwise positivity of rough initial data.
example {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    0 < potentialHeatSolution ν (fun s y => sin (s+y)) (fun x => exp |x|) 0 x :=
  potentialHeatSolution_pos (T := 0) hν (fun _ _ => by fun_prop)
    (fun k _ => sine_cont k 0) (fun k _ => sine_bound k 0)
    (by fun_prop) exp_abs_growth (fun _ => exp_pos _) ⟨le_rfl,le_rfl⟩ x
