/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersExponentialGrowth
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Set MeasureTheory Real
open scoped ContDiff Interval
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

open Filter Topology ColeHopf

example (u₀ : ℝ → ℝ) (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (x₀ x : ℝ) :
    Tendsto (fun t => burgersSolution ν u₀ x₀ t x) (𝓝[>] 0) (𝓝 (u₀ x)) :=
  burgersSolution_tendsto_zero_of_bounded hu hb hν x₀ x

-- Nonzero constant velocity: the simplest case excluded by a primitive lower bound.
example (ν c x₀ x : ℝ) (hν : 0 < ν) :
    Tendsto (fun t => burgersSolution ν (fun _ => c) x₀ t x) (𝓝[>] 0) (𝓝 c) :=
  burgersSolution_tendsto_zero_of_bounded continuous_const ⟨|c|, fun _ => le_rfl⟩ hν x₀ x

example : ¬ (∃ L : ℝ, ∀ x, L ≤ ∫ _y in (0 : ℝ)..x, (1 : ℝ)) := by
  rintro ⟨L, hL⟩
  have h := hL (L - 1)
  simp at h
  linarith

-- The same construction is exactly constant, not only a formal initial trace.
example (ν c x₀ t x : ℝ) (hν : 0 < ν) : burgersSolution ν (fun _ => c) x₀ t x = c := by
  let f := initialHeatProfile ν (fun _ => c) x₀
  have hg : HasExpGrowth f := initialHeatProfile_hasExpGrowth ⟨|c|, fun _ => le_rfl⟩ hν x₀
  have hdg : HasExpGrowth (deriv f) :=
    initialHeatProfile_deriv_hasExpGrowth continuous_const ⟨|c|, fun _ => le_rfl⟩ hν x₀
  have hd : deriv f = fun y => (-c / (2 * ν)) * f y :=
    funext (fun y => (initialHeatProfile_hasDerivAt continuous_const ν x₀ y).deriv)
  have hp : heatSolution f (ν * t) x ≠ 0 := ne_of_gt
    (heatSolution_pos_of_exp_growth (initialHeatProfile_contDiff continuous_const ν x₀).continuous
      hg (initialHeatProfile_pos ν (fun _ => c) x₀) (ν * t) x)
  change -2 * ν * (deriv (heatSolution f (ν * t)) x / heatSolution f (ν * t) x) = c
  rw [(heatSolution_hasDerivAt_deriv_of_exp_growth
    (initialHeatProfile_contDiff continuous_const ν x₀) hg hdg (ν * t) x).deriv,
    hd, heatSolution_const_mul]
  field_simp

-- A bounded nonconstant velocity with primitive unbounded below.
private noncomputable def velocity (x : ℝ) : ℝ := 1 + sin x

private theorem velocity_continuous : Continuous velocity := by unfold velocity; fun_prop

private theorem velocity_bound : ∃ M, ∀ x, |velocity x| ≤ M := by
  refine ⟨2, fun x => ?_⟩
  calc
    |velocity x| ≤ |(1 : ℝ)| + |sin x| := abs_add_le _ _
    _ ≤ 2 := by norm_num; linarith [abs_sin_le_one x]

example : ¬ (∃ L : ℝ, ∀ x, L ≤ ∫ y in (0 : ℝ)..x, velocity y) := by
  rintro ⟨L, hL⟩
  have h := hL (L - 3)
  simp only [velocity, intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    (continuous_sin.intervalIntegrable _ _), intervalIntegral.integral_const, integral_sin,
    cos_zero, sub_zero, smul_eq_mul, mul_one] at h
  linarith [neg_one_le_cos (L - 3)]

example : Tendsto (fun t => burgersSolution 3 velocity 7 t (π / 2)) (𝓝[>] 0) (𝓝 2) := by
  simpa only [velocity, sin_pi_div_two, one_add_one_eq_two] using
    burgersSolution_tendsto_zero_of_bounded velocity_continuous velocity_bound
      (by norm_num : (0 : ℝ) < 3) 7 (π / 2)

example (ν x₀ t x : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    deriv (fun s => burgersSolution ν velocity x₀ s x) t +
      burgersSolution ν velocity x₀ t x * deriv (burgersSolution ν velocity x₀ t) x =
        ν * iteratedDeriv 2 (burgersSolution ν velocity x₀ t) x :=
  burgersSolution_burgers_of_bounded velocity_continuous velocity_bound hν x₀ t x ht

example : ContDiffOn ℝ 2 (Function.uncurry (burgersSolution 3 velocity 7)) (Ioi 0 ×ˢ univ) :=
  burgersSolution_contDiffOn_of_bounded velocity_continuous velocity_bound (by norm_num) 7

example : DifferentiableAt ℝ (Function.uncurry (burgersSolution 3 velocity 7)) (1, 0) := by
  have hc := burgersSolution_contDiffOn_of_bounded velocity_continuous velocity_bound
    (by norm_num : (0 : ℝ) < 3) 7
  exact (hc.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
    ⟨by norm_num, mem_univ _⟩)).differentiableAt (by norm_num)

-- The initial extension and the limiting theorem agree at a nonzero value.
example : burgersSolution 3 velocity 7 0 (π / 2) = 2 := by
  rw [burgersSolution_zero velocity_continuous (by norm_num)]
  norm_num [velocity]

-- Bounded continuous data need not have a derivative: the cusp is admissible.
example (ν x₀ x : ℝ) (hν : 0 < ν) :
    Tendsto (fun t => burgersSolution ν (fun y => |sin y|) x₀ t x) (𝓝[>] 0) (𝓝 |sin x|) :=
  burgersSolution_tendsto_zero_of_bounded continuous_sin.abs
    ⟨1, fun y => by simpa only [abs_abs] using abs_sin_le_one y⟩ hν x₀ x

#print axioms ColeHopf.burgersSolution_solves_initial_value_of_bounded
