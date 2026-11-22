/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.ForcedInverseColeHopf
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped ContDiff

-- The potential enters with a positive sign in the normalization rate.
example : ColeHopf.forcedNormalizationRate 2 (fun _ _ => 4) (fun _ _ => 3) 5 7 = 5 := by
  norm_num [ColeHopf.forcedNormalizationRate, ColeHopf.normalizationRate]

example (ν : ℝ) (u : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) :
    ColeHopf.forcedInverseProfile ν u (fun _ _ => 0) t₀ x₀ t x =
      ColeHopf.inverseProfile ν u t₀ x₀ t x :=
  ColeHopf.forcedInverseProfile_zero ν u t₀ x₀ t x

example (ν : ℝ) (u F : ℝ → ℝ → ℝ) (t₀ x₀ : ℝ) :
    ColeHopf.forcedInverseProfile ν u F t₀ x₀ t₀ x₀ = 1 := by simp

example (ν : ℝ) (u F : ℝ → ℝ → ℝ) (t₀ x₀ t x : ℝ) :
    0 < ColeHopf.forcedInverseProfile ν u F t₀ x₀ t x :=
  ColeHopf.forcedInverseProfile_pos ν u F t₀ x₀ t x

-- Recovery does not require a forced Burgers premise.
example (t x : ℝ) :
    ColeHopf.classicalTransform 2
      (ColeHopf.forcedInverseProfile 2 (fun t x => t * x) (fun t x => t + x) 3 5) t x =
      t * x :=
  ColeHopf.classicalTransform_forcedInverseProfile 2 (by norm_num) _ _ 3 5 t x (by fun_prop)

example : ColeHopf.classicalTransform 0
    (ColeHopf.forcedInverseProfile 0 (fun _ _ => 1) (fun t x => t + x) 0 0) 0 0 ≠ 1 := by
  simp [ColeHopf.classicalTransform]

-- A profile with nonzero mixed derivatives and genuinely spatially varying forcing.
private noncomputable def profile (t x : ℝ) : ℝ := Real.exp (t * x + x ^ 2)
private def potential (t x : ℝ) : ℝ := x - 2 - (t + 2 * x) ^ 2
private def velocity (t x : ℝ) : ℝ := -2 * (t + 2 * x)

private theorem profile_smooth : ContDiff ℝ 3 (Function.uncurry profile) := by
  unfold profile Function.uncurry
  fun_prop

private theorem profile_pos (t x : ℝ) : 0 < profile t x := Real.exp_pos _

private theorem profile_dx (t : ℝ) : deriv (profile t) = fun x => (t + 2 * x) * profile t x := by
  funext x
  have h : HasDerivAt (fun y : ℝ => Real.exp (t * y + y ^ 2))
      (Real.exp (t * x + x ^ 2) * (t + 2 * x)) x := by
    simpa using! (((hasDerivAt_id' x).const_mul t).add ((hasDerivAt_id' x).pow 2)).exp
  change deriv (fun y : ℝ => Real.exp (t * y + y ^ 2)) x = _
  rw [h.deriv]
  exact mul_comm _ _

private theorem profile_heat (t x : ℝ) :
    deriv (fun s => profile s x) t = iteratedDeriv 2 (profile t) x +
      potential t x * profile t x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, profile_dx]
  have hd := ((hasDerivAt_id' x).const_mul 2).const_add t
  have hp : HasDerivAt (profile t) ((t + 2 * x) * profile t x) x := by
    have h : HasDerivAt (profile t) (deriv (profile t) x) x :=
      ((profile_smooth.differentiable (by norm_num)).comp
        ((differentiable_const t).prodMk differentiable_id) x).hasDerivAt
    simpa only [profile_dx] using h
  have hxx : HasDerivAt (fun y => (t + 2 * y) * profile t y)
      (2 * profile t x + (t + 2 * x) * ((t + 2 * x) * profile t x)) x := by
    simpa using! hd.mul hp
  rw [hxx.deriv]
  simp [profile, potential]
  ring

private theorem profile_transform : ColeHopf.classicalTransform 1 profile = velocity := by
  funext t x
  unfold ColeHopf.classicalTransform velocity
  rw [profile_dx]
  simp [ne_of_gt (profile_pos t x)]

private theorem velocity_dx (t : ℝ) : deriv (velocity t) = fun _ => -4 := by
  funext x
  change deriv (fun y : ℝ => -2 * (t + 2 * y)) x = -4
  norm_num

private theorem potential_dx (t : ℝ) :
    deriv (potential t) = fun x => 1 - 4 * (t + 2 * x) := by
  funext x
  have h : HasDerivAt (fun y : ℝ => y - 2 - (t + 2 * y) ^ 2)
      (1 - 2 * (t + 2 * x) * 2) x := by
    simpa using! ((hasDerivAt_id' x).sub_const 2).sub
      ((((hasDerivAt_id' x).const_mul 2).const_add t).pow 2)
  change deriv (fun y : ℝ => y - 2 - (t + 2 * y) ^ 2) x = _
  rw [h.deriv]
  ring

private theorem velocity_forced (t x : ℝ) :
    deriv (fun s => velocity s x) t + velocity t x * deriv (velocity t) x =
      1 * iteratedDeriv 2 (velocity t) x - 2 * 1 * deriv (potential t) x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, velocity_dx, potential_dx]
  simp [velocity]
  ring

-- Actual inverse PDE, using a nonzero temporal and spatial origin.
example (t x : ℝ) :
    deriv (fun s => ColeHopf.forcedInverseProfile 1 velocity potential 2 3 s x) t =
      iteratedDeriv 2 (ColeHopf.forcedInverseProfile 1 velocity potential 2 3 t) x +
        potential t x * ColeHopf.forcedInverseProfile 1 velocity potential 2 3 t x := by
  simpa using ColeHopf.forcedInverseProfile_heat 1 (by norm_num) velocity potential
    (by unfold velocity Function.uncurry; fun_prop)
    (by unfold potential Function.uncurry; fun_prop) 2 3 t x (velocity_forced t)

example (t₀ x₀ t x : ℝ) :
    ColeHopf.forcedInverseProfile 1 velocity potential t₀ x₀ t x =
      profile t x / profile t₀ x₀ := by
  rw [← profile_transform]
  exact ColeHopf.forcedInverseProfile_classicalTransform 1 (by norm_num) profile potential
    profile_smooth profile_pos (by intro t x; simpa using profile_heat t x) t₀ x₀ t x

-- At the base point (1,2), the rate is 2 while the spatial curvature is 27.
example : HasDerivAt
    (fun t => ColeHopf.forcedInverseProfile 1 velocity potential 1 2 t 2) 2 1 := by
  have h := ColeHopf.forcedInverseProfile_hasDerivAt_t 1 (by norm_num) velocity potential
    (by unfold velocity Function.uncurry; fun_prop)
    (by unfold potential Function.uncurry; fun_prop) 1 2 1 2 (velocity_forced 1)
  norm_num [ColeHopf.forcedNormalizationRate, ColeHopf.normalizationRate, velocity_dx, velocity, potential] at h ⊢
  exact h

example : iteratedDeriv 2 (ColeHopf.forcedInverseProfile 1 velocity potential 1 2 1) 2 = 27 := by
  have h := ColeHopf.forcedInverseProfile_iteratedDeriv_two 1 velocity potential
    (by unfold velocity Function.uncurry; fun_prop) 1 2 1 2
  norm_num [velocity_dx, velocity] at h ⊢
  exact h

-- A time-only potential has zero spatial forcing but nontrivial normalization.
example (t₀ x₀ t x : ℝ) :
    ColeHopf.forcedInverseProfile 2 (fun _ _ => 0) (fun s _ => s) t₀ x₀ t x =
      Real.exp ((t ^ 2 - t₀ ^ 2) / 2) := by
  simp [ColeHopf.forcedInverseProfile, ColeHopf.forcedInversePotential,
    ColeHopf.forcedNormalizationRate, ColeHopf.normalizationRate]

-- The general time-potential shift law is usable with a spatially varying base potential.
example (t x : ℝ) :
    ColeHopf.forcedInverseProfile 1 velocity (fun s y => potential s y + s) 0 0 t x =
      Real.exp (t ^ 2 / 2) * ColeHopf.forcedInverseProfile 1 velocity potential 0 0 t x := by
  have h := ColeHopf.forcedInverseProfile_add_timePotential 1 velocity potential (fun s => s)
    (by unfold velocity Function.uncurry; fun_prop)
    (by unfold potential Function.uncurry; fun_prop) continuous_id 0 0 t x
  simpa using h

-- Constant scaling, including a signed profile, preserves the forward transform.
example : ColeHopf.classicalTransform 1 (fun t x => -3 * profile t x) = velocity := by
  rw [ColeHopf.classicalTransform_const_mul 1 (-3) (by norm_num), profile_transform]

private theorem scaled_profile_heat (c t x : ℝ) :
    deriv (fun s => c * profile s x) t = iteratedDeriv 2 (fun y => c * profile t y) x +
      potential t x * (c * profile t x) := by
  rw [deriv_const_mul_field, iteratedDeriv_const_mul_field, profile_heat]
  ring

-- Scale uniqueness for a nonconstant solution, with every PDE premise discharged.
example : ∃! c : ℝ, 0 < c ∧ ∀ t x, 3 * profile t x = c * profile t x := by
  apply ColeHopf.potentialProfiles_existsUnique_scale 1 (by norm_num)
    (fun t x => 3 * profile t x) profile potential
    (by unfold profile Function.uncurry; fun_prop) profile_smooth
    (fun t x => mul_pos (by norm_num) (profile_pos t x)) profile_pos
    (by intro t x; simpa using scaled_profile_heat 3 t x)
    (by intro t x; simpa using profile_heat t x)
  exact ColeHopf.classicalTransform_const_mul 1 3 (by norm_num) profile

-- Arbitrary-origin normalization removes the scale of a nonconstant profile.
example (t₀ x₀ t x : ℝ) :
    (3 * profile t x) / (3 * profile t₀ x₀) = profile t x / profile t₀ x₀ := by
  exact ColeHopf.potentialProfiles_normalized_eq 1 (by norm_num)
    (fun t x => 3 * profile t x) profile potential
    (by unfold profile Function.uncurry; fun_prop) profile_smooth
    (fun t x => mul_pos (by norm_num) (profile_pos t x)) profile_pos
    (by intro t x; simpa using scaled_profile_heat 3 t x)
    (by intro t x; simpa using profile_heat t x)
    (ColeHopf.classicalTransform_const_mul 1 3 (by norm_num) profile) t₀ x₀ t x

-- Any positive regular solution with this potential, transform and base value
-- equals the explicit profile; this tests the useful uniqueness endpoint.
example (ψ : ℝ → ℝ → ℝ) (hψ : ContDiff ℝ 3 (Function.uncurry ψ))
    (hp : ∀ t x, 0 < ψ t x)
    (hh : ∀ t x, deriv (fun s => ψ s x) t = iteratedDeriv 2 (ψ t) x + potential t x * ψ t x)
    (he : ColeHopf.classicalTransform 1 ψ = velocity) (hb : ψ 2 3 = profile 2 3) :
    ψ = profile := by
  apply ColeHopf.potentialProfiles_eq_of_base_eq 1 (by norm_num) ψ profile potential
    hψ profile_smooth hp profile_pos (by intro t x; simpa using hh t x)
    (by intro t x; simpa using profile_heat t x) _ 2 3 hb
  rw [profile_transform]
  exact he

-- Negative nonzero viscosity is supported; this is not a forward parabolic claim.
example (t x : ℝ) :
    deriv (fun s => ColeHopf.forcedInverseProfile (-2) (fun _ _ => 0) (fun s _ => s) 1 3 s x) t =
      -2 * iteratedDeriv 2
        (ColeHopf.forcedInverseProfile (-2) (fun _ _ => 0) (fun s _ => s) 1 3 t) x +
      t * ColeHopf.forcedInverseProfile (-2) (fun _ _ => 0) (fun s _ => s) 1 3 t x := by
  apply ColeHopf.forcedInverseProfile_heat (-2) (by norm_num) _ _ (by fun_prop) (by fun_prop)
  intro y
  simp

-- Same transform alone permits time-dependent scale: these profiles agree at
-- (0,0) but differ at (1,0), and solve potential equations with F=0 and F=1.
example : ColeHopf.classicalTransform 1 (fun _ _ => (1 : ℝ)) =
    ColeHopf.classicalTransform 1 (fun t _ => Real.exp t) ∧
    Real.exp (0 : ℝ) = 1 ∧ Real.exp (1 : ℝ) ≠ 1 := by
  refine ⟨?_, by simp, ?_⟩
  · funext t x
    simp [ColeHopf.classicalTransform]
  · exact ne_of_gt (Real.one_lt_exp_iff.mpr (by norm_num))

example (t x : ℝ) :
    deriv (fun s => Real.exp s) t =
      iteratedDeriv 2 (fun _ : ℝ => Real.exp t) x + 1 * Real.exp t := by
  simp [iteratedDeriv_succ, iteratedDeriv_zero]

-- At zero viscosity the same-potential condition cannot restore injectivity.
example : ColeHopf.classicalTransform 0 (fun _ _ => (1 : ℝ)) =
    ColeHopf.classicalTransform 0 (fun _ x => Real.exp x) ∧
    (∀ t x : ℝ, deriv (fun _ : ℝ => Real.exp x) t =
      0 * iteratedDeriv 2 Real.exp x) ∧ Real.exp (1 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ne_of_gt (Real.one_lt_exp_iff.mpr (by norm_num))⟩
  · funext t x
    simp [ColeHopf.classicalTransform]
  · intro t x
    simp

-- Strict positivity is substantive: the zero and unit heat profiles have the
-- same transform, but no positive constant can scale the unit profile to zero.
example : ColeHopf.classicalTransform 1 (fun _ _ => (0 : ℝ)) =
    ColeHopf.classicalTransform 1 (fun _ _ => (1 : ℝ)) ∧
    ¬ ∃ c : ℝ, 0 < c ∧ (0 : ℝ) = c * 1 := by
  constructor
  · funext t x
    simp [ColeHopf.classicalTransform]
  · simp
