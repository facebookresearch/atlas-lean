/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelUniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Topology Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatWholeLine
open MathlibExt.Analysis.PDE.HeatKernel

private theorem exp_growth : HasExpGrowth exp := by
  simpa only [one_mul] using HasExpGrowth.exp_linear 1

-- Arbitrary strip length and diffusivity: the constants are not just pointwise in time.
example {f : ℝ → ℝ} (hf : Continuous f) (hg : HasExpGrowth f) {ν : ℝ} (hν : 0 ≤ ν)
    (T : ℝ) : ∃ M c : ℝ, 0 ≤ M ∧ 0 ≤ c ∧
      ∀ t ∈ Icc 0 T, ∀ x, |heatSolution f (ν * t) x| ≤ M * exp (c * |x|) :=
  heatSolution_hasExpGrowthOnStrip hf hg hν T

-- Signed, spatially unbounded data and a small positive viscosity.
example (T : ℝ) : HasExpGrowthOnStrip
    (fun t x => heatSolution (fun y => -3 * exp (2 * y)) (t / 100) x) T := by
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using!
    heatSolution_hasExpGrowthOnStrip (by fun_prop) ((HasExpGrowth.exp_linear 2).const_mul (-3))
      (by norm_num : (0 : ℝ) ≤ 1 / 100) T

private theorem corner_growth : HasExpGrowth (fun x : ℝ => exp |x|) := by
  refine ⟨1, 1, by norm_num, by norm_num, fun x => ?_⟩
  simp only [one_mul, abs_of_pos (exp_pos _), le_refl]

-- Nondifferentiable initial data are allowed; zero scaling remains a stationary profile.
example (T : ℝ) : HasExpGrowthOnStrip (fun t x => heatSolution (fun y => exp |y|) (0 * t) x) T :=
  heatSolution_hasExpGrowthOnStrip (by fun_prop) corner_growth (by norm_num) T

-- An actual exponentially growing classical heat mode at nonunit viscosity.
private noncomputable def mode (t x : ℝ) : ℝ := exp (3 * t) * exp x

private theorem mode_dxx (t x : ℝ) : iteratedDeriv 2 (mode t) x = mode t x := by
  change iteratedDeriv 2 (fun y => exp (3 * t) • exp y) x = _
  rw [iteratedDeriv_fun_const_smul_field]
  simp only [iteratedDeriv_eq_iterate, iter_deriv_exp, smul_eq_mul, mode]

private theorem mode_time (t x : ℝ) : HasDerivAt (fun s => mode s x) (3 * mode t x) t := by
  convert (((hasDerivAt_id' t).const_mul 3).exp.mul_const (exp x)) using 1
  · rfl
  · dsimp [mode]; ring

private theorem mode_growth (T : ℝ) : HasExpGrowthOnStrip mode T := by
  refine ⟨exp (3 * max T 0), 1, (exp_pos _).le, by norm_num, fun t ht x => ?_⟩
  change |exp (3 * t) * exp x| ≤ _
  rw [abs_of_pos (mul_pos (exp_pos _) (exp_pos _)), one_mul]
  exact mul_le_mul (exp_le_exp.mpr (by linarith [ht.2, le_max_left T 0]))
    (exp_le_exp.mpr (le_abs_self x)) (exp_pos _).le (exp_pos _).le

example (T : ℝ) : ∀ t ∈ Icc 0 T, ∀ x,
    heatSolution exp (3 * t) x = exp (3 * t) * exp x := by
  have h := eq_heatSolution_of_exp_growth (u := mode) (ut := fun t x => 3 * mode t x)
    (by norm_num : (0 : ℝ) < 3) continuous_exp exp_growth
    (by unfold mode; fun_prop) (by intros; unfold mode; fun_prop)
    (fun t _ x => (mode_time t x).hasDerivWithinAt)
    (fun t _ x => by rw [mode_dxx]) (mode_growth T) (by intro x; simp [mode])
  exact fun t ht x => (h t ht x).symm

-- The final endpoint follows from a left time derivative, with arbitrary spatial position.
example (x : ℝ) : heatSolution exp 6 x = exp 6 * exp x := by
  have h := eq_heatSolution_of_exp_growth (u := mode) (ut := fun t x => 3 * mode t x)
    (T := 2) (by norm_num : (0 : ℝ) < 3) continuous_exp exp_growth
    (by unfold mode; fun_prop) (by intros; unfold mode; fun_prop)
    (fun t _ x => (mode_time t x).hasDerivWithinAt)
    (fun t _ x => by rw [mode_dxx]) (mode_growth 2) (by intro x; simp [mode])
  simpa only [mode, show (3 : ℝ) * 2 = 6 by norm_num] using!
    (h 2 (by constructor <;> norm_num) x).symm

-- A genuinely nonsmooth initial velocity profile needs no derivative at time zero.
example {u ut : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hpde : ∀ t ∈ Ioc 0 T, ∀ x, ut t x = ν * iteratedDeriv 2 (u t) x)
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) (h₀ : ∀ x, u 0 x = |sin x|) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x = heatSolution (fun y => |sin y|) (ν * t) x := by
  exact eq_heatSolution_of_exp_growth hν continuous_sin.abs
    (HasExpGrowth.of_bounded ⟨1, fun x => by simpa only [abs_abs] using abs_sin_le_one x⟩)
    hc hx ht hpde (HasExpGrowthOnStrip.of_bounded hb) h₀

-- A zero-length strip requires only the initial continuity/value, not positive-time regularity.
example {u : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry u)) (h₀ : ∀ x, u 0 x = exp x) :
    ∀ t ∈ Icc 0 0, ∀ x, u t x = heatSolution exp (7 * t) x := by
  have hg : HasExpGrowthOnStrip u 0 := by
    refine ⟨1, 1, by norm_num, by norm_num, fun t ht x => ?_⟩
    have he : t = 0 := le_antisymm ht.2 ht.1
    rw [he, h₀ x, abs_of_pos (exp_pos _), one_mul, one_mul]
    exact exp_le_exp.mpr (le_abs_self x)
  exact eq_heatSolution_of_exp_growth (ut := fun _ _ => 0) (by norm_num)
    continuous_exp exp_growth hc.continuousOn (by simp) (by simp) (by simp) hg h₀

#print axioms MathlibExt.Analysis.PDE.HeatKernel.heatSolution_hasExpGrowthOnStrip
#print axioms MathlibExt.Analysis.PDE.HeatKernel.eq_heatSolution_of_exp_growth
