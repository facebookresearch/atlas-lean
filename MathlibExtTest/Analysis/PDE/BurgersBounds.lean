/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.BurgersBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open ColeHopf Set Filter Topology

-- Both endpoints of the initial range survive, with arbitrary viscosity and anchor.
example {u₀ : ℝ → ℝ} (hu : Continuous u₀) {a b ν : ℝ} (hν : 0 < ν)
    (h : ∀ x, u₀ x ∈ Icc a b) (x₀ t x : ℝ) :
    burgersSolution ν u₀ x₀ t x ∈ Icc a b :=
  burgersSolution_mem_Icc hu hν h x₀ t x

-- Joint continuity is stronger than the old fixed-position initial limit.
example {u₀ : ℝ → ℝ} (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M)
    {ν : ℝ} (hν : 0 < ν) (x₀ : ℝ) :
    Continuous (Function.uncurry (burgersSolution ν u₀ x₀)) :=
  burgersSolution_continuous_of_bounded hu hb hν x₀

open Real MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel
open scoped ContDiff

-- The interval may collapse to a point: constant velocities stay exactly constant.
example (c ν x₀ t x : ℝ) (hν : 0 < ν) : burgersSolution ν (fun _ => c) x₀ t x = c := by
  have h := burgersSolution_mem_Icc (u₀ := fun _ => c) continuous_const hν
    (a := c) (b := c) (fun _ => ⟨le_rfl, le_rfl⟩) x₀ t x
  exact le_antisymm h.2 h.1

-- A one-sided range is retained, rather than merely its symmetric absolute bound.
example (ν x₀ t x : ℝ) (hν : 0 < ν) :
    burgersSolution ν (fun y => 1 + sin y) x₀ t x ∈ Icc 0 2 := by
  apply burgersSolution_mem_Icc (by fun_prop) hν
  intro y
  constructor <;> linarith [neg_one_le_sin y, sin_le_one y]

-- A strictly negative range tests both signs in the quotient inequality.
example (t x : ℝ) : burgersSolution (1 / 100) (fun y => -2 + sin y) 7 t x ∈ Icc (-3) (-1) := by
  apply burgersSolution_mem_Icc (by fun_prop) (by norm_num)
  intro y
  constructor <;> linarith [neg_one_le_sin y, sin_le_one y]

example (ν x₀ t x : ℝ) (hν : 0 < ν) : |burgersSolution ν sin x₀ t x| ≤ 1 :=
  abs_burgersSolution_le continuous_sin hν abs_sin_le_one x₀ t x

-- Zero initial bound is allowed.
example (ν x₀ t x : ℝ) (hν : 0 < ν) : burgersSolution ν (fun _ => 0) x₀ t x = 0 := by
  have h := abs_burgersSolution_le (u₀ := fun _ => 0) continuous_const hν
    (M := 0) (by simp) x₀ t x
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

-- A bounded continuous but nonsmooth velocity requires no initial derivative hypothesis.
private noncomputable def cornerVelocity (x : ℝ) : ℝ := |sin x|

private theorem corner_continuous : Continuous cornerVelocity := continuous_sin.abs

private theorem corner_bound : ∃ M, ∀ x, |cornerVelocity x| ≤ M :=
  ⟨1, fun x => by simpa only [cornerVelocity, abs_abs] using abs_sin_le_one x⟩

example : ContinuousOn (Function.uncurry (burgersSolution 3 cornerVelocity 7)) (Ici 0 ×ˢ univ) :=
  (burgersSolution_continuous_of_bounded corner_continuous corner_bound
    (by norm_num) 7).continuousOn

example (t x : ℝ) : burgersSolution 3 cornerVelocity 7 t x ∈ Icc 0 1 :=
  burgersSolution_mem_Icc corner_continuous (by norm_num)
    (fun x => ⟨abs_nonneg _, abs_sin_le_one x⟩) 7 t x

-- Joint initial recovery works along a moving spatial path, not only at fixed x.
example (x : ℝ) : Tendsto (fun t : ℝ => burgersSolution 3 cornerVelocity 7 t (x + sqrt t))
    (𝓝[>] 0) (𝓝 (cornerVelocity x)) := by
  have hc : Continuous (fun t : ℝ => (t, x + sqrt t)) := by fun_prop
  have hp : Tendsto (fun t : ℝ => (t, x + sqrt t)) (𝓝[>] 0) (𝓝 (0, x)) := by
    simpa only [sqrt_zero, add_zero] using!
      hc.continuousAt.continuousWithinAt.tendsto (s := Ioi (0 : ℝ)) (x := 0)
  have h := (burgersSolution_tendsto_initial_of_bounded corner_continuous corner_bound
    (by norm_num : (0 : ℝ) < 3) 7 x).comp hp
  simpa only [Function.comp_def, Function.uncurry_def] using! h

-- General-path use does not force differentiability of the path.
example {α : Type*} {l : Filter α} {s y : α → ℝ} {u₀ : ℝ → ℝ}
    (hu : Continuous u₀) (hb : ∃ M, ∀ x, |u₀ x| ≤ M) {ν x₀ x : ℝ} (hν : 0 < ν)
    (hs : Tendsto s l (𝓝 0)) (hy : Tendsto y l (𝓝 x)) :
    Tendsto (fun a => burgersSolution ν u₀ x₀ (s a) (y a)) l (𝓝 (u₀ x)) := by
  have h := (burgersSolution_tendsto_initial_of_bounded hu hb hν x₀ x).comp (hs.prodMk_nhds hy)
  simpa only [Function.comp_def, Function.uncurry_def] using! h

-- The weighted average is an identity for the actual Cole–Hopf solution.
example (ν x₀ t x : ℝ) (hν : 0 < ν) :
    burgersSolution ν sin x₀ t x =
      heatSolution (fun y => sin y * initialHeatProfile ν sin x₀ y) (ν * t) x /
        heatSolution (initialHeatProfile ν sin x₀) (ν * t) x :=
  burgersSolution_eq_weighted_heat continuous_sin ⟨1, abs_sin_le_one⟩ hν x₀ t x

-- Generic profile continuity needs no uniform positive lower bound on the profile.
example (ν : ℝ) : Continuous (Function.uncurry (burgersFromHeat ν exp)) := by
  have hg : HasExpGrowth exp := by simpa only [one_mul] using HasExpGrowth.exp_linear 1
  exact burgersFromHeat_continuous_of_exp_growth contDiff_exp hg
    (by simpa only [Real.deriv_exp] using hg) exp_pos ν

#print axioms ColeHopf.burgersSolution_eq_weighted_heat
#print axioms ColeHopf.burgersSolution_mem_Icc
#print axioms ColeHopf.burgersSolution_continuous_of_bounded
