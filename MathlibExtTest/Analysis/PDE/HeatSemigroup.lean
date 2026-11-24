/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatSemigroup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

open MeasureTheory Set Real
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

-- Continuous data need not be bounded or differentiable for the semigroup law.
example {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ℝ) :
    heatSolution (heatSolution (fun y => exp y) s) t x =
      heatSolution (fun y => exp y) (s+t) x :=
  heatSolution_semigroup_of_exp_growth Real.continuous_exp
    (by simpa using HasExpGrowth.exp_linear 1) hs ht x

private theorem exp_forcing_growth (T : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip (fun _ y => exp y) T := by
  obtain ⟨M,c,hM,hc,hb⟩ := HasExpGrowth.exp_linear (1 : ℝ)
  exact ⟨M,c,hM,hc,fun _ _ y => by simpa using hb y⟩

example {T t : ℝ} (ht : t ∈ Icc 0 T) (h x : ℝ) :
    heatSolution (fun y => ∫ _s in 0..t, exp y) h x =
      ∫ _s in 0..t, heatSolution (fun y => exp y) h x := by
  apply heatSolution_intervalIntegral_of_exp_growth
    (show ContinuousOn (Function.uncurry (fun _ y : ℝ => exp y)) (Icc 0 T ×ˢ univ) by fun_prop)
    (exp_forcing_growth T) ht h x

example {ν T a b : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ T) (x : ℝ) :
    heatDuhamel ν (fun _ y => exp y) (a+b) x =
      heatSolution (heatDuhamel ν (fun _ y => exp y) a) (ν*b) x +
        heatDuhamel ν (fun _ y => exp y) b x := by
  simpa using heatDuhamel_restart hν
    (show ContinuousOn (Function.uncurry (fun _ y : ℝ => exp y)) (Icc 0 T ×ˢ univ) by fun_prop)
    (exp_forcing_growth T) ha hb hab x

-- The initial profile has spatial cusps; no spatial derivative premise is used.
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) :
    heatSolution (heatSolution (fun y => |sin y|) a) b x =
      heatSolution (fun y => |sin y|) (a + b) x :=
  heatSolution_semigroup_of_exp_growth (by fun_prop)
    (HasExpGrowth.of_bounded ⟨1, fun y => by simpa only [abs_abs] using abs_sin_le_one y⟩) ha hb x

example {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    heatSolution (heatSolution (fun y => exp y) 0) t x =
      heatSolution (fun y => exp y) t x := by
  simpa only [zero_add] using heatSolution_semigroup_of_exp_growth Real.continuous_exp
    (by simpa using HasExpGrowth.exp_linear 1) (show (0 : ℝ) ≤ 0 from le_rfl) ht x

example {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    heatSolution (heatSolution (fun y => exp y) s) 0 x =
      heatSolution (fun y => exp y) s x := by
  simpa only [add_zero] using heatSolution_semigroup_of_exp_growth Real.continuous_exp
    (by simpa using HasExpGrowth.exp_linear 1) hs (show (0 : ℝ) ≤ 0 from le_rfl) x

private noncomputable def timeForcing (s x : ℝ) := s * exp x

private theorem time_cont : ContinuousOn (Function.uncurry timeForcing) (Icc 0 2 ×ˢ univ) := by
  unfold timeForcing Function.uncurry
  fun_prop

private theorem time_growth :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip timeForcing 2 := by
  refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
  intro s hs x
  calc
    |timeForcing s x| = s * exp x := by
      simp only [timeForcing, abs_mul, abs_of_nonneg hs.1, abs_of_pos (exp_pos x)]
    _ ≤ 2 * exp |x| := mul_le_mul hs.2 (exp_le_exp.mpr (le_abs_self x))
      (exp_pos x).le (by norm_num)
    _ = 2 * exp (1 * |x|) := by rw [one_mul]

-- The forcing shift matters: the second term uses s + 1, not the original s.
example {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    heatDuhamel ν timeForcing 2 x = heatSolution (heatDuhamel ν timeForcing 1) ν x +
      heatDuhamel ν (fun s y => (1 + s) * exp y) 1 x := by
  simpa only [timeForcing, one_add_one_eq_two, mul_one] using!
    heatDuhamel_restart hν time_cont time_growth
      (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) + 1 ≤ 2 by norm_num) x

example (x : ℝ) : heatDuhamel 0 timeForcing 2 x =
    heatSolution (heatDuhamel 0 timeForcing 1) 0 x +
      heatDuhamel 0 (fun s y => (1 + s) * exp y) 1 x := by
  simpa only [timeForcing, one_add_one_eq_two, zero_mul] using!
    heatDuhamel_restart (show (0 : ℝ) ≤ 0 from le_rfl) time_cont time_growth
      (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) + 1 ≤ 2 by norm_num) x

example {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    heatDuhamel ν timeForcing 2 x = heatSolution (heatDuhamel ν timeForcing 2) 0 x +
      heatDuhamel ν (fun s => timeForcing (2 + s)) 0 x := by
  simpa only [add_zero, mul_zero] using heatDuhamel_restart hν time_cont time_growth
    (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 0 from le_rfl)
    (show (2 : ℝ) + 0 ≤ 2 by norm_num) x

example {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    heatSolution (heatDuhamel ν timeForcing 1) 3 x =
      ∫ s in 0..1, heatSolution (timeForcing s) (ν * (1 - s) + 3) x :=
  heatSolution_heatDuhamel hν time_cont time_growth
    (by constructor <;> norm_num) (by norm_num) x

-- Forcing may be discontinuous outside the closed strip; heat time may be negative.
private noncomputable def cutForcing (s x : ℝ) := if s ∈ Icc (0 : ℝ) 2 then exp x else 0

example (x : ℝ) :
    heatSolution (fun y => ∫ s in 0..2, cutForcing s y) (-1) x =
      ∫ s in 0..2, heatSolution (cutForcing s) (-1) x := by
  have hc : ContinuousOn (Function.uncurry cutForcing) (Icc 0 2 ×ˢ univ) := by
    apply (show ContinuousOn (fun p : ℝ × ℝ => exp p.2) (Icc 0 2 ×ˢ univ) by fun_prop).congr
    intro p hp
    simp only [Function.uncurry_def, cutForcing, ite_eq_left hp.1]
  have hg : MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip cutForcing 2 := by
    obtain ⟨M,c,hM,hc,hb⟩ := exp_forcing_growth 2
    refine ⟨M,c,hM,hc,fun s hs y => ?_⟩
    simpa only [cutForcing, ite_eq_left hs] using hb s hs y
  exact heatSolution_intervalIntegral_of_exp_growth hc hg ⟨by norm_num,le_rfl⟩ (-1) x

-- Restart applies to the full inhomogeneous solution, including nonzero initial data.
example {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    heatSolution (fun y => exp y) (ν * 2) x + heatDuhamel ν timeForcing 2 x =
      heatSolution (fun y => heatSolution (fun z => exp z) ν y + heatDuhamel ν timeForcing 1 y)
        ν x + heatDuhamel ν (fun s => timeForcing (1 + s)) 1 x := by
  simpa only [one_add_one_eq_two, mul_one] using heatSolution_add_heatDuhamel_restart hν
    Real.continuous_exp (by simpa using HasExpGrowth.exp_linear 1) time_cont time_growth
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    (show (1 : ℝ) + 1 ≤ 2 by norm_num) x

example (t x : ℝ) :
    heatSolution (fun y => exp y + exp (-y)) t x =
      heatSolution (fun y => exp y) t x + heatSolution (fun y => exp (-y)) t x :=
  heatSolution_add_of_exp_growth Real.continuous_exp (by fun_prop)
    (by simpa using HasExpGrowth.exp_linear 1)
    (by simpa using HasExpGrowth.exp_linear (-1)) t x
