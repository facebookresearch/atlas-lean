/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersInitialValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

open Filter Topology Set MeasureTheory Real
open scoped ContDiff Interval
open ColeHopf

example (u₀ : ℝ → ℝ) (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    (ν x₀ : ℝ) (hν : 0 < ν)
    (hU : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, u₀ y) (x : ℝ) :
    Tendsto (fun t => burgersSolution ν u₀ x₀ t x) (𝓝[>] 0) (𝓝 (u₀ x)) :=
  burgersSolution_tendsto_zero hu hb hν hU x

-- Prescribed sine velocity: its anchored primitive is bounded below for every anchor.
private theorem sin_primitive_lower (x₀ : ℝ) : ∃ L, ∀ x, L ≤ ∫ y in x₀..x, sin y := by
  refine ⟨cos x₀ - 1, fun x => ?_⟩
  rw [integral_sin]
  linarith [cos_le_one x]

example (ν x₀ x : ℝ) (hν : 0 < ν) :
    Tendsto (fun t => burgersSolution ν sin x₀ t x) (𝓝[>] 0) (𝓝 (sin x)) :=
  burgersSolution_tendsto_zero continuous_sin ⟨1, abs_sin_le_one⟩ hν
    (sin_primitive_lower x₀) x

-- A nonzero recovered value at nonunit viscosity.
example : Tendsto (fun t => burgersSolution 3 sin 0 t (π / 2)) (𝓝[>] 0) (𝓝 1) := by
  simpa only [sin_pi_div_two] using burgersSolution_tendsto_zero continuous_sin
    ⟨1, abs_sin_le_one⟩ (by norm_num : (0 : ℝ) < 3) (sin_primitive_lower 0) (π / 2)

example : burgersSolution 3 sin 0 0 (π / 2) = 1 := by
  rw [burgersSolution_zero continuous_sin (by norm_num), sin_pi_div_two]

example (ν x₀ : ℝ) (hν : 0 < ν) (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => burgersSolution ν sin x₀ s x) t +
      burgersSolution ν sin x₀ t x * deriv (burgersSolution ν sin x₀ t) x =
        ν * iteratedDeriv 2 (burgersSolution ν sin x₀ t) x :=
  burgersSolution_burgers continuous_sin hν (sin_primitive_lower x₀) t x ht

example : ContDiffOn ℝ 2 (Function.uncurry (burgersSolution 3 sin 0)) (Ioi 0 ×ˢ univ) :=
  burgersSolution_contDiffOn continuous_sin (by norm_num) (sin_primitive_lower 0)

-- Actual joint derivatives exist; the PDE cannot rely on default derivative values.
example : DifferentiableAt ℝ (Function.uncurry (burgersSolution 3 sin 0)) (1, 0) := by
  have hc := burgersSolution_contDiffOn continuous_sin
    (by norm_num : (0 : ℝ) < 3) (sin_primitive_lower 0)
  exact (hc.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
    ⟨by norm_num, mem_univ _⟩)).differentiableAt (by norm_num)

-- The exponential formula respects the orientation of the spatial integral.
example (ν x₀ x : ℝ) : initialHeatProfile ν sin x₀ x =
    exp (-(cos x₀ - cos x) / (2 * ν)) := by
  simp only [initialHeatProfile, integral_sin]

example (ν x₀ : ℝ) : initialHeatProfile ν sin x₀ x₀ = 1 := initialHeatProfile_anchor _ _ _

-- Pointwise quotient recovery does not require a globally positive profile.
example : Tendsto (fun t => burgersFromHeat 3 sin t (π / 2)) (𝓝[>] 0) (𝓝 0) := by
  have h := burgersFromHeat_tendsto_zero contDiff_sin ⟨1, abs_sin_le_one⟩
    ⟨1, fun x => by simpa only [Real.deriv_sin] using abs_cos_le_one x⟩
    (by norm_num : (0 : ℝ) < 3) (π / 2) (by rw [sin_pi_div_two]; norm_num)
  simpa only [Real.deriv_sin, cos_pi_div_two, sin_pi_div_two, zero_div, mul_zero] using h

-- A strictly positive nonconstant heat profile, with a negative initial velocity at zero.
private noncomputable def profile (x : ℝ) : ℝ := 2 + sin x

private theorem profile_regular : ContDiff ℝ 1 profile := by unfold profile; fun_prop

private theorem profile_bound : ∃ M, ∀ x, |profile x| ≤ M := by
  refine ⟨3, fun x => ?_⟩
  have h := abs_sin_le_one x
  calc
    |profile x| ≤ |(2 : ℝ)| + |sin x| := abs_add_le _ _
    _ ≤ 3 := by norm_num; linarith

private theorem profile_deriv (x : ℝ) : deriv profile x = cos x := by
  exact ((hasDerivAt_sin x).const_add 2).deriv

private theorem profile_deriv_bound : ∃ M, ∀ x, |deriv profile x| ≤ M :=
  ⟨1, fun x => by rw [profile_deriv]; exact abs_cos_le_one x⟩

example : Tendsto (fun t => burgersFromHeat 3 profile t 0) (𝓝[>] 0) (𝓝 (-3)) := by
  have h := burgersFromHeat_tendsto_zero profile_regular profile_bound profile_deriv_bound
    (by norm_num : (0 : ℝ) < 3) 0 (by norm_num [profile])
  norm_num [profile_deriv, profile] at h ⊢
  exact h

example (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => burgersFromHeat 3 profile s x) t +
      burgersFromHeat 3 profile t x * deriv (burgersFromHeat 3 profile t) x =
        3 * iteratedDeriv 2 (burgersFromHeat 3 profile t) x := by
  apply burgersFromHeat_burgers profile_regular.continuous profile_bound
    (fun y => by dsimp [profile]; linarith [neg_one_le_sin y]) (by norm_num) t x ht

-- Zero velocity is the normalized constant profile and remains zero.
example (x : ℝ) : initialHeatProfile 3 (fun _ => 0) 0 x = 1 := by simp [initialHeatProfile]

example (t x : ℝ) : burgersSolution 3 (fun _ => 0) 0 t x = 0 := by
  have hp : initialHeatProfile 3 (fun _ => 0) 0 = fun _ => 1 := by
    funext y
    simp [initialHeatProfile]
  simp only [burgersSolution, hp, burgersFromHeat, classicalTransform,
    MathlibExt.Analysis.PDE.HeatKernel.heatSolution_const, deriv_const, zero_div, mul_zero]

-- Bounded velocity alone does not imply the sufficient primitive lower bound.
example : ¬ (∃ L : ℝ, ∀ x, L ≤ ∫ _y in (0 : ℝ)..x, (1 : ℝ)) := by
  rintro ⟨L, hL⟩
  have h := hL (L - 1)
  simp at h
  linarith

#print axioms ColeHopf.burgersSolution_solves_initial_value
