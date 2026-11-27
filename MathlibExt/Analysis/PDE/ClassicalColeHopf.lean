/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Classical Cole–Hopf residual identity

For an arbitrary jointly `C³` real profile `φ(t,x)`, the transform
`u = -2ν φₓ/φ` obeys
`uₜ + u uₓ - ν uₓₓ = -2ν ∂ₓ ((φₜ - ν φₓₓ)/φ)` wherever `φ ≠ 0`.
The heat equation and the equation with a spatial potential follow as corollaries.
All derivatives are classical real derivatives. Mixed derivative symmetry is
derived from regularity, rather than required as a separate hypothesis.

The global joint `C³` assumption is a convenient sufficient regularity condition,
stronger than the anisotropic regularity in the reference. Nonvanishing is only
required at the point of evaluation; continuity provides a neighborhood for
differentiating the quotient. The identities allow any real viscosity and either
sign of the profile. They do not construct a heat profile or assert uniqueness.

## References

Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Lemmas 3.1 and 3.2, equations (3.1)–(3.3), and Theorem 3.3(ii),
https://arxiv.org/abs/solv-int/9812025.
The reference uses positive profiles and positive viscosity on positive time;
the quotient calculation below holds on the nonzero locus for all real viscosity.
-/

@[expose] public section

open scoped ContDiff Topology

namespace ColeHopf

private theorem hasDerivAt_space {φ : ℝ → ℝ → ℝ}
    (h : Differentiable ℝ (Function.uncurry φ)) (t x : ℝ) :
    HasDerivAt (φ t) (fderiv ℝ (Function.uncurry φ) (t, x) (0, 1)) x := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
    (h (t, x)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))

private theorem hasDerivAt_time {φ : ℝ → ℝ → ℝ}
    (h : Differentiable ℝ (Function.uncurry φ)) (t x : ℝ) :
    HasDerivAt (fun s => φ s x) (fderiv ℝ (Function.uncurry φ) (t, x) (1, 0)) t := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
    (h (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

private theorem contDiff_space {φ : ℝ → ℝ → ℝ} {m n : ℕ∞ω}
    (h : ContDiff ℝ n (Function.uncurry φ)) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContDiff ℝ m (Function.uncurry (fun t x => deriv (φ t) x)) := by
  change ContDiff ℝ m (fun p : ℝ × ℝ => deriv (φ p.1) p.2)
  have heq : (fun p : ℝ × ℝ => deriv (φ p.1) p.2) =
      (fun p => fderiv ℝ (Function.uncurry φ) p (0, 1)) :=
    funext fun p => (hasDerivAt_space (h.differentiable hn) p.1 p.2).deriv
  rw [heq]
  exact (h.fderiv_right hm).clm_apply contDiff_const

private theorem contDiff_time {φ : ℝ → ℝ → ℝ} {m n : ℕ∞ω}
    (h : ContDiff ℝ n (Function.uncurry φ)) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContDiff ℝ m (Function.uncurry (fun t x => deriv (fun s => φ s x) t)) := by
  change ContDiff ℝ m (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1)
  have heq : (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) =
      (fun p => fderiv ℝ (Function.uncurry φ) p (1, 0)) :=
    funext fun p => (hasDerivAt_time (h.differentiable hn) p.1 p.2).deriv
  rw [heq]
  exact (h.fderiv_right hm).clm_apply contDiff_const

private theorem mixed_deriv_eq {φ : ℝ → ℝ → ℝ}
    (h : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ) :
    deriv (fun s => deriv (φ s) x) t =
      deriv (fun y => deriv (fun s => φ s y) t) x := by
  let f := Function.uncurry φ
  have hd := h.differentiable (by norm_num)
  have hfd := (h.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have he (v w : ℝ × ℝ) :
      fderiv ℝ (fun p => fderiv ℝ f p v) (t, x) w =
        fderiv ℝ (fderiv ℝ f) (t, x) w v := by
    have hh := (hfd (t, x)).hasFDerivAt.clm_apply (hasFDerivAt_const v (t, x))
    simpa using congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) hh.fderiv
  simp_rw [(hasDerivAt_space hd _ _).deriv, (hasDerivAt_time hd _ _).deriv]
  rw [(hasDerivAt_time (φ := fun t x => fderiv ℝ f (t, x) (0, 1))
    ((h.fderiv_right (m := 2) (by norm_num)).clm_apply
    contDiff_const |>.differentiable (by norm_num)) t x).deriv,
    (hasDerivAt_space (φ := fun t x => fderiv ℝ f (t, x) (1, 0))
      ((h.fderiv_right (m := 2) (by norm_num)).clm_apply
    contDiff_const |>.differentiable (by norm_num)) t x).deriv]
  exact (he (0, 1) (1, 0)).trans
    (((h.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1)).trans
      (he (1, 0) (0, 1)).symm)

/-- Classical Cole–Hopf transform. At zeros this uses total real division;
the differential identities require a nonzero profile value. -/
noncomputable def classicalTransform (ν : ℝ) (φ : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -2 * ν * (deriv (φ t) x / φ t x)

/-- The transform is jointly `C²` at each nonzero point of a `C³` profile. -/
theorem classicalTransform_contDiffAt (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (p : ℝ × ℝ) (h : φ p.1 p.2 ≠ 0) :
    ContDiffAt ℝ 2 (Function.uncurry (classicalTransform ν φ)) p :=
  contDiffAt_const.mul ((contDiff_space hφ (by norm_num) (by norm_num)).contDiffAt.div
    (hφ.of_le (by norm_num)).contDiffAt h)

private theorem space_derivative {φ : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (h : ContDiff ℝ n (Function.uncurry φ)) (hn : n ≠ 0) (t x : ℝ) :
    HasDerivAt (φ t) (deriv (φ t) x) x :=
  (hasDerivAt_space (h.differentiable hn) t x).differentiableAt.hasDerivAt

private theorem time_derivative {φ : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (h : ContDiff ℝ n (Function.uncurry φ)) (hn : n ≠ 0) (t x : ℝ) :
    HasDerivAt (fun s => φ s x) (deriv (fun s => φ s x) t) t :=
  (hasDerivAt_time (h.differentiable hn) t x).differentiableAt.hasDerivAt

/-- Spatial quotient rule for the classical transform. -/
theorem classicalTransform_hasDerivAt_x (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ) (h : φ t x ≠ 0) :
    HasDerivAt (classicalTransform ν φ t)
      (-2 * ν * ((deriv (deriv (φ t)) x * φ t x -
        deriv (φ t) x * deriv (φ t) x) / φ t x ^ 2)) x := by
  have hx := contDiff_space hφ (by norm_num) (m := 2) (by norm_num)
  exact ((space_derivative hx (by norm_num) t x).div
    (space_derivative hφ (by norm_num) t x) h).const_mul (-2 * ν)

/-- Time quotient rule; the mixed derivative is the derivative of the time slice. -/
theorem classicalTransform_hasDerivAt_t (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ) (h : φ t x ≠ 0) :
    HasDerivAt (fun s => classicalTransform ν φ s x)
      (-2 * ν * ((deriv (fun y => deriv (fun s => φ s y) t) x * φ t x -
        deriv (φ t) x * deriv (fun s => φ s x) t) / φ t x ^ 2)) t := by
  have hx := contDiff_space hφ (by norm_num) (m := 2) (by norm_num)
  have hd := ((time_derivative hx (by norm_num) t x).div
    (time_derivative hφ (by norm_num) t x) h).const_mul (-2 * ν)
  simpa only [mixed_deriv_eq hφ t x] using! hd

/-- Second spatial quotient derivative, justified on the local nonzero locus. -/
theorem classicalTransform_iteratedDeriv_two (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ) (h : φ t x ≠ 0) :
    iteratedDeriv 2 (classicalTransform ν φ t) x =
      -2 * ν * (deriv (deriv (deriv (φ t))) x / φ t x -
        3 * deriv (φ t) x * deriv (deriv (φ t)) x / φ t x ^ 2 +
        2 * deriv (φ t) x ^ 3 / φ t x ^ 3) := by
  have hx := contDiff_space hφ (by norm_num) (m := 2) (by norm_num)
  have hxx := contDiff_space hx (by norm_num) (m := 1) (by norm_num)
  have h0 := space_derivative hφ (by norm_num) t x
  have h1 := space_derivative hx (by norm_num) t x
  have h2 := space_derivative hxx (by norm_num) t x
  have hd := (((h2.mul h0).sub (h1.mul h1)).div
    (h0.pow 2) (pow_ne_zero 2 h)).const_mul (-2 * ν)
  have heq : deriv (classicalTransform ν φ t) =ᶠ[𝓝 x]
      (fun y => -2 * ν * ((deriv (deriv (φ t)) y * φ t y -
        deriv (φ t) y * deriv (φ t) y) / φ t y ^ 2)) := by
    filter_upwards [h0.continuousAt.eventually_ne h] with y hy
    exact (classicalTransform_hasDerivAt_x ν φ hφ t y hy).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    (hd.congr_of_eventuallyEq heq).deriv]
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

/-- Cole–Hopf intertwines the classical Burgers and normalized heat residuals. -/
theorem classicalTransform_residual (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ) (h : φ t x ≠ 0) :
    deriv (fun s => classicalTransform ν φ s x) t +
        classicalTransform ν φ t x * deriv (classicalTransform ν φ t) x -
        ν * iteratedDeriv 2 (classicalTransform ν φ t) x =
      -2 * ν * deriv (fun y =>
        (deriv (fun s => φ s y) t - ν * iteratedDeriv 2 (φ t) y) / φ t y) x := by
  have hx := contDiff_space hφ (by norm_num) (m := 2) (by norm_num)
  have hxx := contDiff_space hx (by norm_num) (m := 1) (by norm_num)
  have ht := contDiff_time hφ (by norm_num) (m := 2) (by norm_num)
  have hd := ((space_derivative ht (by norm_num) t x).sub
    ((space_derivative hxx (by norm_num) t x).const_mul ν)).div
      (space_derivative hφ (by norm_num) t x) h
  rw [(classicalTransform_hasDerivAt_t ν φ hφ t x h).deriv,
    (classicalTransform_hasDerivAt_x ν φ hφ t x h).deriv,
    classicalTransform_iteratedDeriv_two ν φ hφ t x h]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hd' : deriv (fun y =>
      (deriv (fun s => φ s y) t - ν * deriv (deriv (φ t)) y) / φ t y) x =
      ((deriv (fun y => deriv (fun s => φ s y) t) x -
        ν * deriv (deriv (deriv (φ t))) x) * φ t x -
        (deriv (fun s => φ s x) t - ν * deriv (deriv (φ t)) x) * deriv (φ t) x) /
        φ t x ^ 2 := hd.deriv
  rw [hd']
  unfold classicalTransform
  field_simp
  ring

/-- A heat equation on a spatial neighborhood gives Burgers at the point. -/
theorem classicalTransform_burgers (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ) (h : φ t x ≠ 0)
    (hheat : ∀ᶠ y in 𝓝 x,
      deriv (fun s => φ s y) t = ν * iteratedDeriv 2 (φ t) y) :
    deriv (fun s => classicalTransform ν φ s x) t +
      classicalTransform ν φ t x * deriv (classicalTransform ν φ t) x =
        ν * iteratedDeriv 2 (classicalTransform ν φ t) x := by
  have heq : (fun y =>
      (deriv (fun s => φ s y) t - ν * iteratedDeriv 2 (φ t) y) / φ t y) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hheat] with y hy
    simp [hy]
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  have hr := classicalTransform_residual ν φ hφ t x h
  rw [hz.deriv, mul_zero] at hr
  exact sub_eq_zero.mp hr

/-- A heat equation with potential `F` gives Burgers with forcing `-2ν Fₓ`.
Only spatial differentiability of `F` at the evaluation point is required. -/
theorem classicalTransform_forced_burgers (ν : ℝ) (φ F : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 3 (Function.uncurry φ)) (t x : ℝ) (h : φ t x ≠ 0)
    (hF : DifferentiableAt ℝ (F t) x)
    (hheat : ∀ᶠ y in 𝓝 x,
      deriv (fun s => φ s y) t = ν * iteratedDeriv 2 (φ t) y + F t y * φ t y) :
    deriv (fun s => classicalTransform ν φ s x) t +
        classicalTransform ν φ t x * deriv (classicalTransform ν φ t) x -
        ν * iteratedDeriv 2 (classicalTransform ν φ t) x =
      -2 * ν * deriv (F t) x := by
  have hn := (space_derivative hφ (by norm_num) t x).continuousAt.eventually_ne h
  have heq : (fun y =>
      (deriv (fun s => φ s y) t - ν * iteratedDeriv 2 (φ t) y) / φ t y) =ᶠ[𝓝 x]
        F t := by
    filter_upwards [hheat, hn] with y hy hny
    rw [hy]
    field_simp
    ring
  rw [classicalTransform_residual ν φ hφ t x h,
    (hF.hasDerivAt.congr_of_eventuallyEq heq).deriv]

end ColeHopf
