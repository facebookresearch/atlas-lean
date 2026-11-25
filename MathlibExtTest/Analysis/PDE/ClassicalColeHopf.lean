/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.ClassicalColeHopf
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped ContDiff

-- A polynomial heat profile, outside the finite exponential-sum construction.
example (ν t x : ℝ) (h : x ^ 2 + 2 * ν * t + 1 ≠ 0) :
    deriv (fun s => ColeHopf.classicalTransform ν
      (fun t x => x ^ 2 + 2 * ν * t + 1) s x) t +
      ColeHopf.classicalTransform ν (fun t x => x ^ 2 + 2 * ν * t + 1) t x *
        deriv (ColeHopf.classicalTransform ν (fun t x => x ^ 2 + 2 * ν * t + 1) t) x =
      ν * iteratedDeriv 2
        (ColeHopf.classicalTransform ν (fun t x => x ^ 2 + 2 * ν * t + 1) t) x := by
  apply ColeHopf.classicalTransform_burgers ν _ (by fun_prop) t x h
  apply Filter.Eventually.of_forall
  intro y
  have ht := (((hasDerivAt_id' t).const_mul (2 * ν)).const_add (y ^ 2)).add_const 1
  have hxx := (hasDerivAt_id' y).const_mul 2
  rw [ht.deriv, iteratedDeriv_succ, iteratedDeriv_one]
  have he : deriv (fun z : ℝ => z ^ 2 + 2 * ν * t + 1) = (fun z => 2 * z) := by
    funext z
    simp
  rw [he, hxx.deriv]
  ring

private def mixedProfile (t x : ℝ) : ℝ := t * x + 1

private theorem mixedProfile_smooth :
    ContDiff ℝ 3 (Function.uncurry mixedProfile) := by
  unfold mixedProfile Function.uncurry
  fun_prop

private theorem mixedProfile_dx (t : ℝ) : deriv (mixedProfile t) = fun _ => t := by
  funext x
  change deriv (fun y : ℝ => t * y + 1) x = t
  simp

private theorem mixedProfile_dt (t x : ℝ) :
    deriv (fun s => mixedProfile s x) t = x := by
  simp [mixedProfile]

-- A nonzero mixed partial at nonunit viscosity fixes the time-derivative sign.
example : HasDerivAt (fun t => ColeHopf.classicalTransform 2 mixedProfile t 0) (-4) 0 := by
  have h := ColeHopf.classicalTransform_hasDerivAt_t 2 mixedProfile
    mixedProfile_smooth 0 0 (by norm_num [mixedProfile])
  norm_num [mixedProfile_dx, mixedProfile_dt, mixedProfile] at h ⊢
  exact h

-- The spatial quotient is nonlinear even though the profile is affine in space.
example : HasDerivAt (ColeHopf.classicalTransform 2 mixedProfile 1) 4 0 := by
  have h := ColeHopf.classicalTransform_hasDerivAt_x 2 mixedProfile
    mixedProfile_smooth 1 0 (by norm_num [mixedProfile])
  norm_num [mixedProfile_dx, mixedProfile] at h ⊢
  exact h

example : iteratedDeriv 2 (ColeHopf.classicalTransform 2 mixedProfile 1) 0 = -8 := by
  have h := ColeHopf.classicalTransform_iteratedDeriv_two 2 mixedProfile
    mixedProfile_smooth 1 0 (by norm_num [mixedProfile])
  norm_num [mixedProfile_dx, mixedProfile] at h ⊢
  exact h

-- Heat holds at this single point, but its spatial residual derivative is nonzero.
example : deriv (fun t => mixedProfile t 0) 0 =
    2 * iteratedDeriv 2 (mixedProfile 0) 0 := by
  simp [mixedProfile_dt, iteratedDeriv_succ, iteratedDeriv_zero, mixedProfile_dx]

-- Thus a pointwise heat premise alone cannot replace the neighborhood premise.
example :
    deriv (fun t => ColeHopf.classicalTransform 2 mixedProfile t 0) 0 +
        ColeHopf.classicalTransform 2 mixedProfile 0 0 *
          deriv (ColeHopf.classicalTransform 2 mixedProfile 0) 0 -
        2 * iteratedDeriv 2 (ColeHopf.classicalTransform 2 mixedProfile 0) 0 = -4 := by
  rw [ColeHopf.classicalTransform_residual 2 mixedProfile mixedProfile_smooth
    0 0 (by norm_num [mixedProfile])]
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero, mixedProfile_dx, mixedProfile]

-- Local smoothness does not require a globally nonvanishing profile.
example : ContDiffAt ℝ 2
    (Function.uncurry (ColeHopf.classicalTransform 2 mixedProfile)) (1, 0) :=
  ColeHopf.classicalTransform_contDiffAt 2 mixedProfile mixedProfile_smooth _ (by
    norm_num [mixedProfile])

-- Negative profiles are admitted, with no positivity premise.
example (ν : ℝ) : ColeHopf.classicalTransform ν (fun _ x => -(x + 1)) 0 0 = -2 * ν := by
  simp [ColeHopf.classicalTransform]

-- Apply the PDE theorem itself at a negative denominator, for any real viscosity.
example (ν : ℝ) :
    deriv (fun t => ColeHopf.classicalTransform ν (fun _ x => -(x + 1)) t 0) 0 +
      ColeHopf.classicalTransform ν (fun _ x => -(x + 1)) 0 0 *
        deriv (ColeHopf.classicalTransform ν (fun _ x => -(x + 1)) 0) 0 =
      ν * iteratedDeriv 2 (ColeHopf.classicalTransform ν (fun _ x => -(x + 1)) 0) 0 := by
  apply ColeHopf.classicalTransform_burgers ν _ (by fun_prop) 0 0 (by norm_num)
  apply Filter.Eventually.of_forall
  intro y
  simp [iteratedDeriv_succ, iteratedDeriv_zero]

-- Viscosity zero is an algebraic degenerate case, including at profile zeros.
example (φ : ℝ → ℝ → ℝ) (t x : ℝ) : ColeHopf.classicalTransform 0 φ t x = 0 := by
  simp [ColeHopf.classicalTransform]

-- A zero profile is totalized but cannot meet the nonvanishing hypothesis.
example (ν : ℝ) : ColeHopf.classicalTransform ν (fun _ x => x) 0 0 = 0 ∧
    ¬ ((fun (_ : ℝ) (x : ℝ) => x) 0 0 ≠ 0) := by
  simp [ColeHopf.classicalTransform]

private theorem expMixed_dx (t : ℝ) :
    deriv (fun x : ℝ => Real.exp (t * x)) = fun x => t * Real.exp (t * x) := by
  funext x
  simpa [mul_comm] using (((hasDerivAt_id' x).const_mul t).exp).deriv

private theorem expMixed_dxx (t x : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.exp (t * x)) x =
      t ^ 2 * Real.exp (t * x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, expMixed_dx]
  rw [((((hasDerivAt_id' x).const_mul t).exp).const_mul t).deriv]
  ring

-- A genuinely spatially varying potential: F(t,x) = x - ν t².
-- The resulting forcing is -2ν, and the profile exp(tx) is everywhere positive.
example (ν t x : ℝ) :
    deriv (fun s => ColeHopf.classicalTransform ν (fun t x => Real.exp (t * x)) s x) t +
        ColeHopf.classicalTransform ν (fun t x => Real.exp (t * x)) t x *
          deriv (ColeHopf.classicalTransform ν (fun t x => Real.exp (t * x)) t) x -
        ν * iteratedDeriv 2
          (ColeHopf.classicalTransform ν (fun t x => Real.exp (t * x)) t) x = -2 * ν := by
  have h := ColeHopf.classicalTransform_forced_burgers ν
    (fun t x => Real.exp (t * x)) (fun t x => x - ν * t ^ 2)
    (by fun_prop) t x (Real.exp_ne_zero _) (by fun_prop) ?_
  · simpa using h
  · apply Filter.Eventually.of_forall
    intro y
    rw [(((hasDerivAt_id' t).mul_const y).exp).deriv, expMixed_dxx]
    ring

-- Zero viscosity still satisfies the theorem itself, not just its definition.
example (t x : ℝ) (h : mixedProfile t x ≠ 0) :
    deriv (fun s => ColeHopf.classicalTransform 0 mixedProfile s x) t +
      ColeHopf.classicalTransform 0 mixedProfile t x *
        deriv (ColeHopf.classicalTransform 0 mixedProfile t) x -
      0 * iteratedDeriv 2 (ColeHopf.classicalTransform 0 mixedProfile t) x = 0 := by
  simpa using ColeHopf.classicalTransform_residual 0 mixedProfile mixedProfile_smooth t x h
