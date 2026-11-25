/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.PDE.InitialForcedInverseColeHopf
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Abs

open Set Real MeasureTheory
open scoped ContDiff Topology Interval
open ColeHopf

-- Initial normalization does not need any regularity or PDE hypothesis.
example (ν : ℝ) (u q : ℝ → ℝ → ℝ) (a : ℝ) :
    initialForcedInverseNormalization ν u q a 0 = 0 := by simp

example (ν : ℝ) (u q : ℝ → ℝ → ℝ) (a x : ℝ) :
    initialForcedInverseProfile ν u q a 0 x = initialHeatProfile ν (u 0) a x := by simp

example (ν : ℝ) (u : ℝ → ℝ → ℝ) (a t x : ℝ) :
    initialForcedInverseProfile ν u (fun _ _ => 0) a t x = initialInverseProfile ν u a t x := by
  simp

-- The interface needs no second time derivative or mixed derivative of velocity.
example {u q : ℝ → ℝ → ℝ} {ν T t : ℝ}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hut : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1) (Ioo 0 T ×ˢ univ))
    (htime : ∀ s ∈ Ioo 0 T, ∀ y, DifferentiableAt ℝ (fun r => u r y) s)
    (hus : ContDiff ℝ 2 (u t)) (hqx : Differentiable ℝ (q t))
    (ht : t ∈ Ioo 0 T)
    (hb : ∀ y, deriv (fun s => u s y) t + u t y * deriv (u t) y =
      ν * iteratedDeriv 2 (u t) y - 2 * ν * deriv (q t) y)
    (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialForcedInverseProfile ν u q a s x)
      (ν * iteratedDeriv 2 (initialForcedInverseProfile ν u q a t) x +
        q t x * initialForcedInverseProfile ν u q a t x) t :=
  initialForcedInverseProfile_hasDerivAt_potential hu hq hut htime hus hqx ht hb hν a x

-- Spatial inversion allows an entirely arbitrary potential and time dependence.
example (q : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (a t x : ℝ) :
    classicalTransform 3 (initialForcedInverseProfile 3 (fun s _ => f s) q a) t x = f t :=
  classicalTransform_initialForcedInverseProfile continuous_const (by norm_num) a x

-- A nonzero spatially constant potential has a positive, not negative, gauge exponent.
example (u : ℝ → ℝ → ℝ) (a t x : ℝ) :
    initialForcedInverseProfile 3 u (fun _ _ => 2) a t x =
      exp (2*t) * initialInverseProfile 3 u a t x := by
  rw [initialForcedInverseProfile_eq_exp_mul]
  congr 2
  simp
  ring

-- Degenerate strips require neither differentiability nor positive viscosity.
example (u q : ℝ → ℝ → ℝ)
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 0 ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 0 ×ˢ univ)) (a : ℝ) :
    ContinuousOn (Function.uncurry (initialForcedInverseProfile 0 u q a)) (Icc 0 0 ×ˢ univ) :=
  initialForcedInverseProfile_continuousOn le_rfl hu hq 0 a

-- A bounded velocity gives profile growth even when the continuous potential is
-- unbounded in space and nondifferentiable. No PDE is needed for this estimate.
example (T : ℝ) (hT : 0 ≤ T) (a : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (initialForcedInverseProfile 3 (fun _ _ => 1) (fun t x => |t-x|) a) T := by
  apply initialForcedInverseProfile_hasExpGrowthOnStrip hT
    (by fun_prop) (by fun_prop) ?_
  exact ⟨1,fun _ _ _ => by norm_num⟩

-- This velocity is C1 in time, but its time derivative has a corner at t = 1.
-- The potential is genuinely spatially varying and the viscosity is nonunit.
private noncomputable def cornerPrimitive (t : ℝ) : ℝ := ∫ r in 1..t, |r-1|

private theorem cornerPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt cornerPrimitive |t-1| t :=
  ((continuous_abs.comp (continuous_id.sub continuous_const)).integral_hasStrictDerivAt 1 t).hasDerivAt

private theorem cornerPrimitive_continuous : Continuous cornerPrimitive :=
  (show Differentiable ℝ cornerPrimitive from fun t =>
    (cornerPrimitive_hasDerivAt t).differentiableAt).continuous

example (a x : ℝ) :
    HasDerivAt
      (fun s => initialForcedInverseProfile 3 (fun t _ => cornerPrimitive t)
        (fun t y => -(|t-1|/6)*y) a s x) 0 1 := by
  have ht : (1 : ℝ) ∈ Ioo 0 2 := by constructor <;> norm_num
  have hu : ContinuousOn (Function.uncurry (fun t (_ : ℝ) => cornerPrimitive t))
      (Icc 0 2 ×ˢ univ) := (cornerPrimitive_continuous.comp continuous_fst).continuousOn
  have hq : ContinuousOn (Function.uncurry (fun t y : ℝ => -(|t-1|/6)*y))
      (Icc 0 2 ×ˢ univ) := by fun_prop
  have hut : ContinuousOn (fun p : ℝ × ℝ => deriv cornerPrimitive p.1)
      (Ioo 0 2 ×ˢ univ) := by
    simp only [(cornerPrimitive_hasDerivAt _).deriv]
    fun_prop
  have hb (y : ℝ) : deriv cornerPrimitive 1 + cornerPrimitive 1 *
      deriv (fun _ : ℝ => cornerPrimitive 1) y =
      3 * iteratedDeriv 2 (fun _ : ℝ => cornerPrimitive 1) y -
        2*3*deriv (fun z => -(|(1 : ℝ)-1|/6)*z) y := by
    simp [cornerPrimitive_hasDerivAt 1 |>.deriv,iteratedDeriv_succ]
  have h := initialForcedInverseProfile_hasDerivAt_t hu hq hut
    (fun s _ _ => (cornerPrimitive_hasDerivAt s).differentiableAt)
    contDiff_const (by simp) ht hb (by norm_num) a x
  simpa [normalizationRate,cornerPrimitive] using h

-- Confirm that the preceding witness really excludes a second time derivative.
example : ¬ DifferentiableAt ℝ (deriv cornerPrimitive) 1 := by
  intro h
  have he : deriv cornerPrimitive = fun t => |t-1| :=
    funext (fun t => (cornerPrimitive_hasDerivAt t).deriv)
  rw [he] at h
  have h0 : DifferentiableAt ℝ (fun t : ℝ => |t-1|) ((0 : ℝ)+1) := by simpa using h
  have hc := h0.comp 0 (show DifferentiableAt ℝ (fun r : ℝ => r+1) 0 from
    differentiableAt_id.add_const 1)
  exact not_differentiableAt_abs_zero (by simpa [Function.comp_def] using hc)


-- Both the terminal time and the initial trace use only closed-strip continuity.
example {u q : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ)) (a x : ℝ) :
    ContinuousWithinAt (Function.uncurry (initialForcedInverseProfile 3 u q a))
      (Icc 0 T ×ˢ univ) (T,x) :=
  initialForcedInverseProfile_continuousOn hT hu hq 3 a (T,x) ⟨⟨hT,le_rfl⟩,mem_univ x⟩

example {u q : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ)) (a x : ℝ) :
    Filter.Tendsto (Function.uncurry (initialForcedInverseProfile 3 u q a))
      (𝓝[Icc 0 T ×ˢ univ] (0,x)) (𝓝 (initialHeatProfile 3 (u 0) a x)) :=
  initialForcedInverseProfile_tendsto_initial hT hu hq 3 a x

-- Away from the corner, the same witness exercises a nonzero spatial forcing
-- and the final potential-heat PDE, not just the normalization-rate formula.
example (a x : ℝ) :
    HasDerivAt
      (fun s => initialForcedInverseProfile 3 (fun t _ => cornerPrimitive t)
        (fun t y => -(|t-1|/6)*y) a s x)
      (3 * iteratedDeriv 2
        (initialForcedInverseProfile 3 (fun t _ => cornerPrimitive t)
          (fun t y => -(|t-1|/6)*y) a 2) x -
        x/6 * initialForcedInverseProfile 3 (fun t _ => cornerPrimitive t)
          (fun t y => -(|t-1|/6)*y) a 2 x) 2 := by
  have ht : (2 : ℝ) ∈ Ioo 0 3 := by constructor <;> norm_num
  have hu : ContinuousOn (Function.uncurry (fun t (_ : ℝ) => cornerPrimitive t))
      (Icc 0 3 ×ˢ univ) := (cornerPrimitive_continuous.comp continuous_fst).continuousOn
  have hq : ContinuousOn (Function.uncurry (fun t y : ℝ => -(|t-1|/6)*y))
      (Icc 0 3 ×ˢ univ) := by fun_prop
  have hut : ContinuousOn (fun p : ℝ × ℝ => deriv cornerPrimitive p.1)
      (Ioo 0 3 ×ˢ univ) := by
    simp only [(cornerPrimitive_hasDerivAt _).deriv]
    fun_prop
  have hqx : Differentiable ℝ (fun y : ℝ => -(|(2 : ℝ)-1|/6)*y) := by fun_prop
  have hb (y : ℝ) : deriv cornerPrimitive 2 + cornerPrimitive 2 *
      deriv (fun _ : ℝ => cornerPrimitive 2) y =
      3 * iteratedDeriv 2 (fun _ : ℝ => cornerPrimitive 2) y -
        2*3*deriv (fun z => -(|(2 : ℝ)-1|/6)*z) y := by
    norm_num [(cornerPrimitive_hasDerivAt 2).deriv,iteratedDeriv_succ,deriv_const_mul_id']
  have h := initialForcedInverseProfile_hasDerivAt_potential hu hq hut
    (fun s _ _ => (cornerPrimitive_hasDerivAt s).differentiableAt)
    contDiff_const hqx ht hb (by norm_num) a x
  convert h using 1
  norm_num
  ring
