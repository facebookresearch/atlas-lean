/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.InverseColeHopf
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ContDiff

-- A nonzero constant Burgers field needs a nonconstant time normalization.
example (ν c t₀ x₀ t x : ℝ) :
    ColeHopf.inverseProfile ν (fun _ _ => c) t₀ x₀ t x =
      Real.exp ((t - t₀) * (c ^ 2 / (4 * ν)) - (x - x₀) * c / (2 * ν)) := by
  simp [ColeHopf.inverseProfile, ColeHopf.inversePotential, ColeHopf.normalizationRate]
  ring

-- Nonzero origins and nonunit viscosity: value and both derivative directions.
example : ColeHopf.inverseProfile 2 (fun _ _ => 4) 3 5 3 5 = 1 := by simp

example : HasDerivAt (ColeHopf.inverseProfile 2 (fun _ _ => 4) 3 5 3) (-1) 5 := by
  have h := ColeHopf.inverseProfile_hasDerivAt_x 2 (fun _ _ => 4) 3 5 3 5
    continuous_const
  norm_num at h ⊢
  exact h

example : HasDerivAt (fun t => ColeHopf.inverseProfile 2 (fun _ _ => 4) 3 5 t 5) 2 3 := by
  have h := ColeHopf.inverseProfile_hasDerivAt_t 2 (by norm_num) (fun _ _ => 4)
    (by fun_prop) 3 5 3 5 (by intro y; simp [iteratedDeriv_succ, iteratedDeriv_zero])
  norm_num [ColeHopf.normalizationRate] at h ⊢
  exact h

example : iteratedDeriv 2 (ColeHopf.inverseProfile 2 (fun _ _ => 4) 3 5 3) 5 = 1 := by
  have h := ColeHopf.inverseProfile_iteratedDeriv_two 2 (fun _ _ => 4)
    (by fun_prop) 3 5 3 5
  norm_num at h ⊢
  exact h

-- The algebraic inverse also supports negative nonzero viscosity.
example (t x : ℝ) :
    deriv (fun s => ColeHopf.inverseProfile (-2) (fun _ _ => 3) 1 4 s x) t =
      -2 * iteratedDeriv 2 (ColeHopf.inverseProfile (-2) (fun _ _ => 3) 1 4 t) x := by
  apply ColeHopf.inverseProfile_heat (-2) (by norm_num) _ (by fun_prop)
  intro y
  simp [iteratedDeriv_succ, iteratedDeriv_zero]

-- Recovery only needs spatial continuity, not the Burgers equation.
example (t x : ℝ) :
    ColeHopf.classicalTransform 2
      (ColeHopf.inverseProfile 2 (fun t x => t * x) 3 5) t x = t * x :=
  ColeHopf.classicalTransform_inverseProfile 2 (by norm_num) _ 3 5 t x (by fun_prop)

example (ν t₀ x₀ t x : ℝ) (u : ℝ → ℝ → ℝ) :
    0 < ColeHopf.inverseProfile ν u t₀ x₀ t x :=
  ColeHopf.inverseProfile_pos ν u t₀ x₀ t x

example (ν t₀ x₀ x : ℝ) (u : ℝ → ℝ → ℝ) :
    ColeHopf.inverseProfile ν u t₀ x₀ t₀ x =
      Real.exp (-(∫ y in x₀..x, u t₀ y) / (2 * ν)) :=
  ColeHopf.inverseProfile_initial ν u t₀ x₀ x

-- At zero viscosity the totalized definitions do not invert a nonzero field.
example : ColeHopf.classicalTransform 0
    (ColeHopf.inverseProfile 0 (fun _ _ => 1) 0 0) 0 0 ≠ 1 := by
  simp [ColeHopf.classicalTransform]

-- The spatial exponential alone for constant velocity -2 is exp(x).
-- It fails heat at viscosity one: time derivative zero, spatial second derivative one.
example : deriv (fun _ : ℝ => Real.exp (0 : ℝ)) 0 ≠
    iteratedDeriv 2 Real.exp 0 := by
  simp [iteratedDeriv_succ, iteratedDeriv_zero, Real.deriv_exp]

private noncomputable def heatProfile (t x : ℝ) : ℝ := 2 + Real.exp (t + x)

private theorem heatProfile_smooth : ContDiff ℝ 3 (Function.uncurry heatProfile) := by
  unfold heatProfile Function.uncurry
  fun_prop

private theorem heatProfile_pos (t x : ℝ) : 0 < heatProfile t x := by
  unfold heatProfile
  positivity

private theorem heatProfile_dx (t : ℝ) :
    deriv (heatProfile t) = fun x => Real.exp (t + x) := by
  funext x
  change deriv (fun y : ℝ => 2 + Real.exp (t + y)) x = _
  simpa using! ((((hasDerivAt_id' x).const_add t).exp).const_add 2).deriv

private theorem heatProfile_heat (t x : ℝ) :
    deriv (fun s => heatProfile s x) t = iteratedDeriv 2 (heatProfile t) x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, heatProfile_dx]
  have hx : deriv (fun y : ℝ => Real.exp (t + y)) x = Real.exp (t + x) := by
    simpa using! (((hasDerivAt_id' x).const_add t).exp).deriv
  rw [hx]
  simp [heatProfile]

private noncomputable def burgersField := ColeHopf.classicalTransform 1 heatProfile

private theorem burgersField_smooth : ContDiff ℝ 2 (Function.uncurry burgersField) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact ColeHopf.classicalTransform_contDiffAt 1 heatProfile heatProfile_smooth p
    (ne_of_gt (heatProfile_pos p.1 p.2))

private theorem burgersField_burgers (t x : ℝ) :
    deriv (fun s => burgersField s x) t + burgersField t x * deriv (burgersField t) x =
      1 * iteratedDeriv 2 (burgersField t) x := by
  apply ColeHopf.classicalTransform_burgers 1 heatProfile heatProfile_smooth t x
    (ne_of_gt (heatProfile_pos t x))
  exact Filter.Eventually.of_forall fun y => by simpa using heatProfile_heat t y

-- A nonconstant, time-dependent Burgers example exercises the integral construction.
example (t x : ℝ) :
    deriv (fun s => ColeHopf.inverseProfile 1 burgersField 0 0 s x) t =
      iteratedDeriv 2 (ColeHopf.inverseProfile 1 burgersField 0 0 t) x := by
  simpa using ColeHopf.inverseProfile_heat 1 (by norm_num) burgersField
    burgersField_smooth 0 0 t x (burgersField_burgers t)

example (t x : ℝ) :
    ColeHopf.classicalTransform 1 (ColeHopf.inverseProfile 1 burgersField 0 0) t x =
      burgersField t x := by
  apply ColeHopf.classicalTransform_inverseProfile 1 (by norm_num)
  exact burgersField_smooth.continuous.comp (continuous_const.prodMk continuous_id)

-- The reverse round trip retains the spatial/time shape and divides by base-point value three.
example (t x : ℝ) :
    ColeHopf.inverseProfile 1 burgersField 0 0 t x = (2 + Real.exp (t + x)) / 3 := by
  have h := ColeHopf.inverseProfile_classicalTransform 1 (by norm_num) heatProfile
    heatProfile_smooth heatProfile_pos
    (fun s y => by simpa using heatProfile_heat s y) 0 0 t x
  norm_num [burgersField, heatProfile] at h ⊢
  exact h

-- The round trip supports arbitrary origins, not just expansions about zero.
example (t₀ x₀ t x : ℝ) :
    ColeHopf.inverseProfile 1 burgersField t₀ x₀ t x =
      heatProfile t x / heatProfile t₀ x₀ :=
  ColeHopf.inverseProfile_classicalTransform 1 (by norm_num) heatProfile
    heatProfile_smooth heatProfile_pos
    (fun s y => by simpa using heatProfile_heat s y) t₀ x₀ t x

-- Constant positive heat profiles lose their multiplicative scale.
example (c : ℝ) (hc : 0 < c) (t₀ x₀ t x : ℝ) :
    ColeHopf.inverseProfile 2 (ColeHopf.classicalTransform 2 (fun _ _ => c))
      t₀ x₀ t x = 1 := by
  have h := ColeHopf.inverseProfile_classicalTransform 2 (by norm_num) (fun _ _ => c)
    (by fun_prop) (fun _ _ => hc)
    (by intro s y; simp [iteratedDeriv_succ, iteratedDeriv_zero]) t₀ x₀ t x
  simpa [ne_of_gt hc] using h

-- Rescaling a nonconstant positive heat profile leaves its normalized inverse unchanged.
example (c : ℝ) (hc : 0 < c) (t x : ℝ) :
    ColeHopf.inverseProfile 1
      (ColeHopf.classicalTransform 1 (fun s y => c * heatProfile s y)) 0 0 t x =
      (2 + Real.exp (t + x)) / 3 := by
  have he : ColeHopf.classicalTransform 1 (fun s y => c * heatProfile s y) =
      burgersField := by
    funext s y
    have hd : HasDerivAt (heatProfile s) (deriv (heatProfile s) y) y :=
      ((heatProfile_smooth.differentiable (by norm_num)).comp
      ((differentiable_const s).prodMk differentiable_id) y).hasDerivAt
    change -2 * 1 * (deriv (fun z => c * heatProfile s z) y / (c * heatProfile s y)) = _
    rw [(hd.const_mul c).deriv]
    unfold burgersField ColeHopf.classicalTransform
    have hp := ne_of_gt (heatProfile_pos s y)
    have hc' := ne_of_gt hc
    field_simp
  rw [he]
  have h := ColeHopf.inverseProfile_classicalTransform 1 (by norm_num) heatProfile
    heatProfile_smooth heatProfile_pos
    (fun s y => by simpa using heatProfile_heat s y) 0 0 t x
  norm_num [burgersField, heatProfile] at h ⊢
  exact h

-- The base rate is determined by the logarithmic time derivative of heat.
example : ColeHopf.normalizationRate 1 burgersField 0 0 = 1 / 3 := by
  have h := ColeHopf.normalizationRate_classicalTransform 1 (by norm_num) heatProfile
    heatProfile_smooth 0 0 (ne_of_gt (heatProfile_pos 0 0))
    (by simpa using heatProfile_heat 0 0)
  norm_num [burgersField, heatProfile] at h ⊢
  exact h

example : Continuous (ColeHopf.normalizationRate 1 burgersField 0) :=
  ColeHopf.normalizationRate_continuous 1 burgersField burgersField_smooth 0
