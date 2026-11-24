/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.SeparableGuidePotential
public import Physlib.Electromagnetism.Dynamics.IsExtrema
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Separable vacuum Maxwell fields

## i. Overview

For a smooth profile `a : ℝ → ℝ` and a smooth mode
`f : ℝ → ℝ → ℝ`, the separable fields
`E = (0, -a(x) f_t(t, z), 0)` and
`B = (-a(x) f_z(t, z), 0, a'(x) f(t, z))` are studied through
one-variable derivatives in each coordinate. When `a` satisfies
the profile equation `a'' = -kc^2 a` and `f` satisfies the mode
equation `f_tt = c^2 (f_zz - kc^2 f)`, the fields satisfy the
source-free vacuum Maxwell equations at a speed of light `c`.
A bridge identifies these component fields with Physlib's
canonical electric and magnetic fields of the separable guide
potential and transfers the result to Physlib's `Space.div`,
`Space.curl` and `Time.deriv`. At the free-space speed of light
the guide potential is an extremum of the free-space Lagrangian
with zero current.

## ii. Key results

- `separableFields_sourceFreeVacuumMaxwell`: the separable
  component fields satisfy the source-free vacuum Maxwell
  equations.
- `sourceFreeVacuumMaxwellFields_of_components`: the bridge from
  the component form to fields on Physlib's `Time` and `Space`.
- `separableGuidePotential_sourceFreeVacuumMaxwellFields`: the
  canonical fields of the separable guide potential satisfy the
  source-free vacuum Maxwell equations.
- `separableFields_isExtrema_withFreeSpace`: the extremum
  form at the free-space speed of light.
- `propagatingMode_sourceFreeVacuumMaxwell` and
  `evanescentMode_sourceFreeVacuumMaxwell`: concrete
  travelling-cosine and exponential modes `exp (-alpha z)`.
- `evanescentMode_decay`: for positive attenuation `0 < alpha`
  the exponential mode is evanescent, decaying strictly and to
  zero along the guide.

## iii. Table of contents

- A. Partial derivatives and the scalar equations
- B. Separable fields and elementary Maxwell operators
- C. Source-free vacuum Maxwell equations
- D. Bridge to Physlib's canonical fields
- E. Extremum form with free-space constants
- F. Failure of the mode equation and concrete modes

## iv. References

- J. D. Jackson, *Classical Electrodynamics*, third edition,
  Wiley, 1998: vacuum Maxwell equations and guided waves.
- R. E. Collin, *Field Theory of Guided Waves*, second
  edition, IEEE Press, 1991: separable waveguide modes.

-/


@[expose] public section

open scoped ContDiff
open SpaceTime Electromagnetism
open PhyslibExt.Electromagnetism.SeparableGuidePotential

namespace PhyslibExt.Electromagnetism.SeparableVacuumMaxwell

/-! ## A. Partial derivatives and the scalar equations -/

/-- Time partial derivative `f_t(t, z)`. -/
noncomputable def partialTime (f : ℝ → ℝ → ℝ) (t z : ℝ) : ℝ := deriv (fun s => f s z) t

/-- Guide-coordinate partial derivative `f_z(t, z)`. -/
noncomputable def partialZ (f : ℝ → ℝ → ℝ) (t z : ℝ) : ℝ := deriv (f t) z

/-- Profile equation `a''(x) = -kc^2 a(x)` for all `x`. -/
def profileEquation (a : ℝ → ℝ) (kc : ℝ) : Prop :=
  ∀ x : ℝ, deriv (deriv a) x = -(kc ^ 2) * a x

/-- Mode equation `f_tt = c0^2 (f_zz - kc^2 f)` for all `t, z`. -/
def modeEquation (c0 kc : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ t z : ℝ, deriv (fun s => partialTime f s z) t =
    c0 ^ 2 * (deriv (fun w => partialZ f t w) z - kc ^ 2 * f t z)

/-! ## B. Separable fields and elementary Maxwell operators -/

/-- Separable electric field, as a function of time and three
space coordinates. -/
noncomputable def separableElectricField (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  fun t x _y z => ![0, -(a x * partialTime f t z), 0]

/-- Separable magnetic field, as a function of time and three
space coordinates. -/
noncomputable def separableMagneticField (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  fun t x _y z => ![-(a x * partialZ f t z), 0, deriv a x * f t z]

/-- Divergence from one-variable derivatives in each space
coordinate. -/
noncomputable def spaceDivergence (F : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ) (t x y z : ℝ) : ℝ :=
  deriv (fun u => F t u y z 0) x + deriv (fun v => F t x v z 1) y +
    deriv (fun w => F t x y w 2) z

/-- Curl from one-variable derivatives in each space
coordinate. -/
noncomputable def spaceCurl (F : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ) (t x y z : ℝ) : Fin 3 → ℝ :=
  ![deriv (fun v => F t x v z 2) y - deriv (fun w => F t x y w 1) z,
    deriv (fun w => F t x y w 0) z - deriv (fun u => F t u y z 2) x,
    deriv (fun u => F t u y z 1) x - deriv (fun v => F t x v z 0) y]

/-- One time-derivative component of a field. -/
noncomputable def timeDerivativeComponent (F : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ)
    (t x y z : ℝ) (i : Fin 3) : ℝ := deriv (fun s => F s x y z i) t

/-- Source-free vacuum Maxwell equations at a speed of light `c`. -/
def sourceFreeVacuumMaxwell (c : SpeedOfLight) (E B : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ) : Prop :=
  ∀ t x y z : ℝ, spaceDivergence E t x y z = 0 ∧ spaceDivergence B t x y z = 0 ∧
    spaceCurl E t x y z = ![-(timeDerivativeComponent B t x y z 0),
      -(timeDerivativeComponent B t x y z 1), -(timeDerivativeComponent B t x y z 2)] ∧
    spaceCurl B t x y z = ![((c : ℝ) ^ 2)⁻¹ * timeDerivativeComponent E t x y z 0,
      ((c : ℝ) ^ 2)⁻¹ * timeDerivativeComponent E t x y z 1,
      ((c : ℝ) ^ 2)⁻¹ * timeDerivativeComponent E t x y z 2]

/-! ## C. Source-free vacuum Maxwell equations -/

private lemma partialTime_eq_fderiv (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    partialTime f t z = fderiv ℝ (Function.uncurry f) (t, z) (1, 0) := by
  have h1 : Differentiable ℝ (Function.uncurry f) := hf.differentiable (by norm_num)
  have hG : HasFDerivAt (Function.uncurry f)
      (fderiv ℝ (Function.uncurry f) (t, z)) (t, z) := (h1 (t, z)).hasFDerivAt
  have hs : HasDerivAt (fun s => (s, z)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have h := hG.comp_hasDerivAt t hs
  have hcomp : (Function.uncurry f) ∘ (fun s => (s, z)) = (fun s => f s z) := rfl
  rw [hcomp] at h
  exact h.deriv

private lemma partialZ_eq_fderiv (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    partialZ f t z = fderiv ℝ (Function.uncurry f) (t, z) (0, 1) := by
  have h1 : Differentiable ℝ (Function.uncurry f) := hf.differentiable (by norm_num)
  have hG : HasFDerivAt (Function.uncurry f)
      (fderiv ℝ (Function.uncurry f) (t, z)) (t, z) := (h1 (t, z)).hasFDerivAt
  have hs : HasDerivAt (fun w => (t, w)) (0, 1) z :=
    (hasDerivAt_const z t).prodMk (hasDerivAt_id z)
  have h := hG.comp_hasDerivAt z hs
  have hcomp : (Function.uncurry f) ∘ (fun w => (t, w)) = (f t) := rfl
  rw [hcomp] at h
  exact h.deriv

private lemma differentiable_fderiv_apply (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (v : ℝ × ℝ) :
    Differentiable ℝ (fun p => fderiv ℝ (Function.uncurry f) p v) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ (Function.uncurry f)) :=
    hf.fderiv_right (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ (Function.uncurry f)) :=
    h1.differentiable (by norm_num)
  intro p
  exact (hd p).clm_apply (differentiableAt_const v)

private lemma differentiableAt_partialTime_left (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    DifferentiableAt ℝ (fun s => partialTime f s z) t := by
  have hfun : (fun s => partialTime f s z) =
      (fun p => fderiv ℝ (Function.uncurry f) p (1, 0)) ∘ (fun s => (s, z)) :=
    funext fun s => partialTime_eq_fderiv f hf s z
  rw [hfun]
  exact (differentiable_fderiv_apply f hf (1, 0) (t, z)).comp t
    ((differentiableAt_id (x := t)).prodMk (differentiableAt_const z))

private lemma differentiableAt_partialZ_right (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    DifferentiableAt ℝ (fun w => partialZ f t w) z := by
  have hfun : (fun w => partialZ f t w) =
      (fun w => fderiv ℝ (Function.uncurry f) (t, w) (0, 1)) :=
    funext fun w => partialZ_eq_fderiv f hf t w
  rw [hfun]
  exact (differentiable_fderiv_apply f hf (0, 1) (t, z)).comp z
    ((differentiableAt_const t).prodMk (differentiableAt_id))

private lemma mixed_partial_eq (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    deriv (fun w => partialTime f t w) z = deriv (fun s => partialZ f s z) t := by
  have hsymm : IsSymmSndFDerivAt ℝ (Function.uncurry f) (t, z) :=
    (hf.contDiffAt (x := (t, z))).isSymmSndFDerivAt (by simp)
  have key := hsymm (0, 1) (1, 0)
  -- Express both sides through the second Fréchet derivative.
  have hleft : deriv (fun w => partialTime f t w) z =
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t, z) (0, 1)) (1, 0) := by
    have hΦ : DifferentiableAt ℝ
        (fun p => fderiv ℝ (Function.uncurry f) p (1, 0)) (t, z) :=
      differentiable_fderiv_apply f hf (1, 0) (t, z)
    have h1 : HasFDerivAt (fun p => fderiv ℝ (Function.uncurry f) p (1, 0))
        ((ContinuousLinearMap.apply ℝ ℝ (1, 0)).comp
          (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t, z))) (t, z) := by
      have hfd : HasFDerivAt (fderiv ℝ (Function.uncurry f))
          (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t, z)) (t, z) := by
        have hd : Differentiable ℝ (fderiv ℝ (Function.uncurry f)) :=
          (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
        exact (hd (t, z)).hasFDerivAt
      exact (ContinuousLinearMap.apply ℝ ℝ (1, 0)).hasFDerivAt.comp (t, z) hfd
    have hs : HasDerivAt (fun w => (t, w)) (0, 1) z :=
      (hasDerivAt_const z t).prodMk (hasDerivAt_id z)
    have h := h1.comp_hasDerivAt z hs
    have hfun : (fun p => fderiv ℝ (Function.uncurry f) p (1, 0)) ∘
        (fun w => (t, w)) = (fun w => partialTime f t w) := by
      funext w
      exact (partialTime_eq_fderiv f hf t w).symm
    rw [hfun] at h
    have hval := h.deriv
    rw [hval]
    rfl
  have hright : deriv (fun s => partialZ f s z) t =
      (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t, z) (1, 0)) (0, 1) := by
    have hΦ : DifferentiableAt ℝ
        (fun p => fderiv ℝ (Function.uncurry f) p (0, 1)) (t, z) :=
      differentiable_fderiv_apply f hf (0, 1) (t, z)
    have h1 : HasFDerivAt (fun p => fderiv ℝ (Function.uncurry f) p (0, 1))
        ((ContinuousLinearMap.apply ℝ ℝ (0, 1)).comp
          (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t, z))) (t, z) := by
      have hfd : HasFDerivAt (fderiv ℝ (Function.uncurry f))
          (fderiv ℝ (fderiv ℝ (Function.uncurry f)) (t, z)) (t, z) := by
        have hd : Differentiable ℝ (fderiv ℝ (Function.uncurry f)) :=
          (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
        exact (hd (t, z)).hasFDerivAt
      exact (ContinuousLinearMap.apply ℝ ℝ (0, 1)).hasFDerivAt.comp (t, z) hfd
    have hs : HasDerivAt (fun s => (s, z)) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
    have h := h1.comp_hasDerivAt t hs
    have hfun : (fun p => fderiv ℝ (Function.uncurry f) p (0, 1)) ∘
        (fun s => (s, z)) = (fun s => partialZ f s z) := by
      funext s
      exact (partialZ_eq_fderiv f hf s z).symm
    rw [hfun] at h
    have hval := h.deriv
    rw [hval]
    rfl
  rw [hleft, hright]
  exact key


/-- Gauss's law for the separable electric field; it holds for
every profile and mode. -/
theorem separable_divergence_electric (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    ∀ t x y z : ℝ, spaceDivergence (separableElectricField a f) t x y z = 0 := by
  intro t x y z
  simp [spaceDivergence, separableElectricField]

/-- Gauss's law for the separable magnetic field; it holds for
every profile and mode. -/
theorem separable_divergence_magnetic (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    ∀ t x y z : ℝ, spaceDivergence (separableMagneticField a f) t x y z = 0 := by
  intro t x y z
  have h1 : deriv (fun u => separableMagneticField a f t u y z 0) x =
      -(deriv a x * partialZ f t z) := by
    have hfun : (fun u => separableMagneticField a f t u y z 0) =
        (fun u => -(a u * partialZ f t z)) := by
      funext u; simp [separableMagneticField]
    rw [hfun, deriv.fun_neg, deriv_mul_const_field]
  have h2 : deriv (fun v => separableMagneticField a f t x v z 1) y = 0 := by
    simp [separableMagneticField]
  have h3 : deriv (fun w => separableMagneticField a f t x y w 2) z =
      deriv a x * partialZ f t z := by
    have hfun : (fun w => separableMagneticField a f t x y w 2) =
        (fun w => deriv a x * f t w) := by
      funext w; simp [separableMagneticField]
    rw [hfun]
    exact deriv_const_mul_field _
  simp [spaceDivergence, h1, h2, h3]

/-- Faraday's law for the separable fields; only the smoothness
of the mode is used, for the symmetry of mixed partials. -/
theorem separable_faraday (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ∀ t x y z : ℝ, spaceCurl (separableElectricField a f) t x y z =
      ![-(timeDerivativeComponent (separableMagneticField a f) t x y z 0),
        -(timeDerivativeComponent (separableMagneticField a f) t x y z 1),
        -(timeDerivativeComponent (separableMagneticField a f) t x y z 2)] := by
  intro t x y z
  have dE_y2 : deriv (fun v => separableElectricField a f t x v z 2) y = 0 := by
    simp [separableElectricField]
  have dE_z1 : deriv (fun w => separableElectricField a f t x y w 1) z =
      -(a x * deriv (fun w => partialTime f t w) z) := by
    have hfun : (fun w => separableElectricField a f t x y w 1) =
        (fun w => -(a x * partialTime f t w)) := by
      funext w; simp [separableElectricField]
    rw [hfun, deriv.fun_neg, deriv_const_mul_field]
  have dE_x1 : deriv (fun u => separableElectricField a f t u y z 1) x =
      -(deriv a x * partialTime f t z) := by
    have hfun : (fun u => separableElectricField a f t u y z 1) =
        (fun u => -(a u * partialTime f t z)) := by
      funext u; simp [separableElectricField]
    rw [hfun, deriv.fun_neg, deriv_mul_const_field]
  have dE_y0 : deriv (fun v => separableElectricField a f t x v z 0) y = 0 := by
    simp [separableElectricField]
  have dE_z0 : deriv (fun w => separableElectricField a f t x y w 0) z = 0 := by
    simp [separableElectricField]
  have dE_x2 : deriv (fun u => separableElectricField a f t u y z 2) x = 0 := by
    simp [separableElectricField]
  have dB_t0 : deriv (fun s => separableMagneticField a f s x y z 0) t =
      -(a x * deriv (fun s => partialZ f s z) t) := by
    have hfun : (fun s => separableMagneticField a f s x y z 0) =
        (fun s => -(a x * partialZ f s z)) := by
      funext s; simp [separableMagneticField]
    rw [hfun, deriv.fun_neg, deriv_const_mul_field]
  have dB_t1 : deriv (fun s => separableMagneticField a f s x y z 1) t = 0 := by
    simp [separableMagneticField]
  have dB_t2 : deriv (fun s => separableMagneticField a f s x y z 2) t =
      deriv a x * partialTime f t z := by
    have hfun : (fun s => separableMagneticField a f s x y z 2) =
        (fun s => deriv a x * f s z) := by
      funext s; simp [separableMagneticField]
    rw [hfun]
    exact deriv_const_mul_field _
  have hmix := mixed_partial_eq f hf t z
  ext i
  fin_cases i <;>
    simp [spaceCurl, timeDerivativeComponent, dE_y2, dE_z1, dE_x1, dE_y0, dE_z0, dE_x2,
      dB_t0, dB_t1, dB_t2, hmix]

/-- Ampère's law for the separable fields; both scalar equations
are used here. -/
theorem separable_ampere (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc : ℝ) (c : SpeedOfLight)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation (c : ℝ) kc f) :
    ∀ t x y z : ℝ, spaceCurl (separableMagneticField a f) t x y z =
      ![((c : ℝ) ^ 2)⁻¹ * timeDerivativeComponent (separableElectricField a f) t x y z 0,
        ((c : ℝ) ^ 2)⁻¹ * timeDerivativeComponent (separableElectricField a f) t x y z 1,
        ((c : ℝ) ^ 2)⁻¹ * timeDerivativeComponent (separableElectricField a f) t x y z 2] := by
  intro t x y z
  have ha_deriv_diff : Differentiable ℝ (deriv a) :=
    (contDiff_infty_iff_deriv.mp ha).2.differentiable (by norm_num)
  have dB_y2 : deriv (fun v => separableMagneticField a f t x v z 2) y = 0 := by
    simp [separableMagneticField]
  have dB_z1 : deriv (fun w => separableMagneticField a f t x y w 1) z = 0 := by
    simp [separableMagneticField]
  have dB_z0 : deriv (fun w => separableMagneticField a f t x y w 0) z =
      -(a x * deriv (fun w => partialZ f t w) z) := by
    have hfun : (fun w => separableMagneticField a f t x y w 0) =
        (fun w => -(a x * partialZ f t w)) := by
      funext w; simp [separableMagneticField]
    rw [hfun]
    exact ((differentiableAt_partialZ_right f hf t z).hasDerivAt.const_mul (a x)).neg.deriv
  have dB_x2 : deriv (fun u => separableMagneticField a f t u y z 2) x =
      deriv (deriv a) x * f t z := by
    have hfun : (fun u => separableMagneticField a f t u y z 2) =
        (fun u => deriv a u * f t z) := by
      funext u; simp [separableMagneticField]
    rw [hfun]
    exact ((ha_deriv_diff x).hasDerivAt.mul_const _).deriv
  have dB_x1 : deriv (fun u => separableMagneticField a f t u y z 1) x = 0 := by
    simp [separableMagneticField]
  have dB_y0 : deriv (fun v => separableMagneticField a f t x v z 0) y = 0 := by
    simp [separableMagneticField]
  have dE_t0 : deriv (fun s => separableElectricField a f s x y z 0) t = 0 := by
    simp [separableElectricField]
  have dE_t1 : deriv (fun s => separableElectricField a f s x y z 1) t =
      -(a x * deriv (fun s => partialTime f s z) t) := by
    have hfun : (fun s => separableElectricField a f s x y z 1) =
        (fun s => -(a x * partialTime f s z)) := by
      funext s; simp [separableElectricField]
    rw [hfun]
    exact ((differentiableAt_partialTime_left f hf t z).hasDerivAt.const_mul (a x)).neg.deriv
  have dE_t2 : deriv (fun s => separableElectricField a f s x y z 2) t = 0 := by
    simp [separableElectricField]
  ext i
  fin_cases i
  · simp [spaceCurl, timeDerivativeComponent, dB_y2, dB_z1, dE_t0]
  · simp [spaceCurl, timeDerivativeComponent, dB_z0, dB_x2, dE_t1, hprofile x, hmode t z]
    have hc : ((c : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt c.pos)
    field_simp
    ring
  · simp [spaceCurl, timeDerivativeComponent, dB_x1, dB_y0, dE_t2]


/-- **Source-free vacuum Maxwell equations for the separable
fields.** -/
theorem separableFields_sourceFreeVacuumMaxwell (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc : ℝ)
    (c : SpeedOfLight) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation (c : ℝ) kc f) :
    sourceFreeVacuumMaxwell c (separableElectricField a f) (separableMagneticField a f) := by
  intro t x y z
  exact ⟨separable_divergence_electric a f t x y z,
    separable_divergence_magnetic a f t x y z,
    separable_faraday a f hf t x y z,
    separable_ampere a f kc c ha hf hprofile hmode t x y z⟩

/-! ## D. Bridge to Physlib's canonical fields -/

/-- Source-free vacuum Maxwell equations at a speed of light `c`
for fields on Physlib's `Time` and `Space`, stated with Physlib's
`Space.div`, `Space.curl` and `Time.deriv`. -/
def sourceFreeVacuumMaxwellFields (c : SpeedOfLight)
    (E B : Time → Space → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ (t : Time) (x : Space), Space.div (E t) x = 0 ∧ Space.div (B t) x = 0 ∧
    Space.curl (E t) x = -Time.deriv (fun s => B s x) t ∧
    Space.curl (B t) x = ((c : ℝ) ^ 2)⁻¹ • Time.deriv (fun s => E s x) t

private lemma space_deriv_eq_deriv_line (g : Space → ℝ) (p : Space)
    (hg : DifferentiableAt ℝ g p) (μ : Fin 3) :
    Space.deriv μ g p = deriv (fun s : ℝ => g (p + s • Space.basis μ)) 0 := by
  have hl : HasDerivAt (fun s : ℝ => p + s • Space.basis μ) (Space.basis μ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Space.basis μ)).const_add p
  exact ((hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)).deriv).symm

private lemma space_deriv_coords (F : ℝ → ℝ → ℝ → ℝ) (g : Space → ℝ)
    (hg : ∀ q, g q = F (q 0) (q 1) (q 2)) (p : Space) (hd : DifferentiableAt ℝ g p) :
    Space.deriv 0 g p = deriv (fun u => F u (p 1) (p 2)) (p 0) ∧
      Space.deriv 1 g p = deriv (fun v => F (p 0) v (p 2)) (p 1) ∧
      Space.deriv 2 g p = deriv (fun w => F (p 0) (p 1) w) (p 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [space_deriv_eq_deriv_line g p hd]
  · simpa [hg, Space.basis_apply] using deriv_comp_const_add (fun u => F u (p 1) (p 2)) (p 0) 0
  · simpa [hg, Space.basis_apply] using deriv_comp_const_add (fun v => F (p 0) v (p 2)) (p 1) 0
  · simpa [hg, Space.basis_apply] using deriv_comp_const_add (fun w => F (p 0) (p 1) w) (p 2) 0

/-- Operator bridge: for a differentiable field `G` on `Time` and
`Space` with components `G s q i = F s (q 0) (q 1) (q 2) i`,
Physlib's divergence, curl and time derivative of `G` are the
coordinate operators of section B applied to `F`. -/
lemma div_curl_deriv_eq_of_components (G : Time → Space → EuclideanSpace ℝ (Fin 3))
    (F : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ) (hG : ∀ s q i, G s q i = F s.val (q 0) (q 1) (q 2) i)
    (hd : Differentiable ℝ ↿G) (t : Time) (p : Space) :
    Space.div (G t) p = spaceDivergence F t.val (p 0) (p 1) (p 2) ∧
      (∀ i, Space.curl (G t) p i = spaceCurl F t.val (p 0) (p 1) (p 2) i) ∧
      ∀ i, Time.deriv (fun s => G s p) t i =
        timeDerivativeComponent F t.val (p 0) (p 1) (p 2) i := by
  have hsp : ∀ i, DifferentiableAt ℝ (fun q => G t q i) p := fun i =>
    ((differentiable_euclidean.mp hd i).comp
      ((differentiable_const t).prodMk differentiable_id)) p
  have htd : Differentiable ℝ (fun s => G s p) :=
    hd.comp (differentiable_id.prodMk (differentiable_const p))
  have hc := fun i => space_deriv_coords (fun u v w => F t.val u v w i) (fun q => G t q i)
    (fun q => hG t q i) p (hsp i)
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · simp only [Space.div, Fin.sum_univ_three, (hc 0).1, (hc 1).2.1, (hc 2).2.2, spaceDivergence]
  · fin_cases i <;>
      simp [Space.curl, spaceCurl, (hc 0).2.1, (hc 0).2.2, (hc 1).1, (hc 1).2.2, (hc 2).1,
        (hc 2).2.1]
  · rw [← Time.deriv_euclid htd t]
    have h := Time.hasDerivAt_mk_of_differentiableAt
      (f := fun s => G s p i) ((differentiable_euclidean.mp htd i) t)
    simp only [hG] at h ⊢
    exact h.deriv.symm

/-- **Bridge to Physlib's canonical fields.** Differentiable
fields on `Time` and `Space` whose components are `FE` and `FB`
satisfy the canonical source-free vacuum Maxwell equations
whenever `FE` and `FB` satisfy the component form. -/
lemma sourceFreeVacuumMaxwellFields_of_components (c : SpeedOfLight)
    (E B : Time → Space → EuclideanSpace ℝ (Fin 3)) (FE FB : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ)
    (hE : ∀ s q i, E s q i = FE s.val (q 0) (q 1) (q 2) i)
    (hB : ∀ s q i, B s q i = FB s.val (q 0) (q 1) (q 2) i)
    (hEd : Differentiable ℝ ↿E) (hBd : Differentiable ℝ ↿B)
    (h : sourceFreeVacuumMaxwell c FE FB) : sourceFreeVacuumMaxwellFields c E B := by
  intro t p
  obtain ⟨hdivE, hdivB, hfar, hamp⟩ := h t.val (p 0) (p 1) (p 2)
  obtain ⟨dE, cE, tE⟩ := div_curl_deriv_eq_of_components E FE hE hEd t p
  obtain ⟨dB, cB, tB⟩ := div_curl_deriv_eq_of_components B FB hB hBd t p
  refine ⟨dE.trans hdivE, dB.trans hdivB, ?_, ?_⟩
  · ext i
    rw [cE i, hfar, PiLp.neg_apply, tB i]
    fin_cases i <;> rfl
  · ext i
    rw [cB i, hamp, PiLp.smul_apply, smul_eq_mul, tE i]
    fin_cases i <;> rfl

/-- The canonical electric field of the separable guide potential
has the separable components. -/
lemma separableGuidePotential_electricField_apply (c : SpeedOfLight) (a : ℝ → ℝ)
    (f : ℝ → ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (s : Time) (q : Space) (i : Fin 3) :
    (separableGuidePotential c a f).electricField c s q i =
      separableElectricField a f s.val (q 0) (q 1) (q 2) i := by
  rw [(separableGuidePotential_fields c a f ha hf).1 s q]
  fin_cases i <;> simp [separableElectricField, partialTime]

/-- The canonical magnetic field of the separable guide potential
has the separable components. -/
lemma separableGuidePotential_magneticField_apply (c : SpeedOfLight) (a : ℝ → ℝ)
    (f : ℝ → ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (s : Time) (q : Space) (i : Fin 3) :
    (separableGuidePotential c a f).magneticField c s q i =
      separableMagneticField a f s.val (q 0) (q 1) (q 2) i := by
  rw [(separableGuidePotential_fields c a f ha hf).2.1 s q]
  fin_cases i <;> simp [separableMagneticField, partialZ]

private lemma differentiable_uncurry_magneticField (c : SpeedOfLight)
    (A : ElectromagneticPotential) (hA : ContDiff ℝ 2 A) :
    Differentiable ℝ ↿(A.magneticField c) := by
  rw [ElectromagneticPotential.magneticField_eq_magneticFieldMatrix A
    (hA.differentiable (by simp)), differentiable_euclidean]
  intro i
  exact (ElectromagneticPotential.magneticFieldMatrix_differentiable A hA _).neg

/-- **Source-free vacuum Maxwell equations for the canonical
fields.** For `C^∞` `a` and `f` satisfying the profile and mode
equations at speed `c`, Physlib's electric and magnetic fields of
the separable guide potential satisfy the source-free vacuum
Maxwell equations. -/
theorem separableGuidePotential_sourceFreeVacuumMaxwellFields (c : SpeedOfLight)
    (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc : ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation (c : ℝ) kc f) :
    sourceFreeVacuumMaxwellFields c ((separableGuidePotential c a f).electricField c)
      ((separableGuidePotential c a f).magneticField c) := by
  have hA := contDiff_separableGuidePotential c a f ha hf
  exact sourceFreeVacuumMaxwellFields_of_components c _ _ _ _
    (separableGuidePotential_electricField_apply c a f ha hf)
    (separableGuidePotential_magneticField_apply c a f ha hf)
    ((ElectromagneticPotential.electricField_contDiff (n := 1)
      (hA.of_le (by simp))).differentiable (by simp))
    (differentiable_uncurry_magneticField c _ (hA.of_le (by simp)))
    (separableFields_sourceFreeVacuumMaxwell a f kc c ha hf hprofile hmode)

/-! ## E. Extremum form with free-space constants -/

/-- **Extremum form with the free-space constants.** The canonical
fields satisfy the source-free equations at the free-space speed
of light, the separable potential is an extremum with zero
current, and the potential and zero current are smooth. -/
theorem separableFields_isExtrema_withFreeSpace
    (𝓕 : FreeSpace) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc : ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc)
    (hmode : modeEquation ((𝓕.c : ℝ)) kc f) :
    sourceFreeVacuumMaxwellFields 𝓕.c ((separableGuidePotential 𝓕.c a f).electricField 𝓕.c)
        ((separableGuidePotential 𝓕.c a f).magneticField 𝓕.c) ∧
      (separableGuidePotential 𝓕.c a f).IsExtrema 𝓕 0 ∧
      ContDiff ℝ ∞ (separableGuidePotential 𝓕.c a f) ∧
      ContDiff ℝ ∞ (0 : LorentzCurrentDensity) := by
  have hA := contDiff_separableGuidePotential 𝓕.c a f ha hf
  have hJ0 : ContDiff ℝ ∞ (0 : LorentzCurrentDensity) := contDiff_zero_fun
  have hM := separableGuidePotential_sourceFreeVacuumMaxwellFields 𝓕.c a f kc ha hf
    hprofile hmode
  refine ⟨hM, ?_, hA, hJ0⟩
  rw [ElectromagneticPotential.isExtrema_iff_gauss_ampere_magneticFieldMatrix hA 0 hJ0]
  intro t p
  obtain ⟨hdivE, -, -, hamp⟩ := hM t p
  refine ⟨?_, fun i => ?_⟩
  · simp only [LorentzCurrentDensity.chargeDensity_zero, Pi.zero_apply, zero_div]
    exact hdivE
  · have hsum : (∑ j, Space.deriv j
        ((separableGuidePotential 𝓕.c a f).magneticFieldMatrix 𝓕.c t · (j, i)) p) =
        Space.curl ((separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p i :=
      (ElectromagneticPotential.magneticField_curl_eq_magneticFieldMatrix
        (separableGuidePotential 𝓕.c a f) (hA.of_le (by simp)) t).symm
    have hμε : 𝓕.μ₀ * 𝓕.ε₀ = ((𝓕.c : ℝ) ^ 2)⁻¹ := by
      rw [FreeSpace.c_sq]
      simp [mul_comm]
    simp only [LorentzCurrentDensity.currentDensity_zero, Pi.zero_apply, PiLp.zero_apply,
      mul_zero, sub_zero]
    rw [hsum, hamp, PiLp.smul_apply, smul_eq_mul, hμε]

/-! ## F. Failure of the mode equation and concrete modes -/

/-- A dispersion mismatch at a point where `a` is nonzero breaks
the source-free Maxwell equations: the Ampère residual is
nonzero. -/
theorem not_sourceFree_of_modeEquation_failure (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc : ℝ)
    (c : SpeedOfLight) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (t x z : ℝ) (hax : a x ≠ 0)
    (hmismatch : deriv (fun s => partialTime f s z) t ≠
      (c : ℝ) ^ 2 * (deriv (fun w => partialZ f t w) z - kc ^ 2 * f t z)) :
    ¬ sourceFreeVacuumMaxwell c (separableElectricField a f) (separableMagneticField a f) := by
  intro h
  apply hmismatch
  have hpoint := h t x 0 z
  obtain ⟨_, _, _, hamp⟩ := hpoint
  have ha_deriv_diff : Differentiable ℝ (deriv a) :=
    (contDiff_infty_iff_deriv.mp ha).2.differentiable (by norm_num)
  have dB_z0 : deriv (fun w => separableMagneticField a f t x 0 w 0) z =
      -(a x * deriv (fun w => partialZ f t w) z) := by
    have hfun : (fun w => separableMagneticField a f t x 0 w 0) =
        (fun w => -(a x * partialZ f t w)) := by
      funext w; simp [separableMagneticField]
    rw [hfun]
    exact ((differentiableAt_partialZ_right f hf t z).hasDerivAt.const_mul (a x)).neg.deriv
  have dB_x2 : deriv (fun u => separableMagneticField a f t u 0 z 2) x =
      deriv (deriv a) x * f t z := by
    have hfun : (fun u => separableMagneticField a f t u 0 z 2) =
        (fun u => deriv a u * f t z) := by
      funext u; simp [separableMagneticField]
    rw [hfun]
    exact ((ha_deriv_diff x).hasDerivAt.mul_const _).deriv
  have dE_t1 : deriv (fun s => separableElectricField a f s x 0 z 1) t =
      -(a x * deriv (fun s => partialTime f s z) t) := by
    have hfun : (fun s => separableElectricField a f s x 0 z 1) =
        (fun s => -(a x * partialTime f s z)) := by
      funext s; simp [separableElectricField]
    rw [hfun]
    exact ((differentiableAt_partialTime_left f hf t z).hasDerivAt.const_mul (a x)).neg.deriv
  have hcomp := congrFun hamp 1
  simp only [spaceCurl, timeDerivativeComponent, dB_z0, dB_x2, dE_t1] at hcomp
  -- `hcomp` is now the component equation at index `1`; simplify its vector entries.
  simp at hcomp
  rw [hprofile x] at hcomp
  have hc : ((c : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt c.pos)
  have h2 := congrArg (fun r => -((c : ℝ) ^ 2) * r) hcomp
  field_simp at h2
  convert h2.symm using 1
  ring

private lemma sin_profileEquation (kc : ℝ) :
    profileEquation (fun x => Real.sin (kc * x)) kc := by
  intro x
  have hd1 : deriv (fun x => Real.sin (kc * x)) =
      fun x => kc * Real.cos (kc * x) := by
    funext y
    have h := (Real.hasDerivAt_sin (kc * y)).comp y ((hasDerivAt_id y).const_mul kc)
    have hd := h.deriv
    change deriv (fun x => Real.sin (kc * x)) y = _ at hd
    rw [hd]
    ring
  rw [hd1]
  show deriv (fun x => kc * Real.cos (kc * x)) x = -(kc ^ 2) * Real.sin (kc * x)
  have h := ((Real.hasDerivAt_cos (kc * x)).comp x
    ((hasDerivAt_id x).const_mul kc)).const_mul kc
  have hd := h.deriv
  change deriv (fun x => kc * Real.cos (kc * x)) x = _ at hd
  rw [hd]
  ring

private lemma partialTime_cos_mode (freq beta t z : ℝ) :
    partialTime (fun t z => Real.cos (freq * t - beta * z)) t z =
      -freq * Real.sin (freq * t - beta * z) := by
  unfold partialTime
  show deriv (fun s => Real.cos (freq * s - beta * z)) t =
    -freq * Real.sin (freq * t - beta * z)
  have hinner : HasDerivAt (fun s => freq * s - beta * z) freq t := by
    simpa using ((hasDerivAt_id t).const_mul freq).sub_const (beta * z)
  have h := (Real.hasDerivAt_cos (freq * t - beta * z)).comp t hinner
  have hd := h.deriv
  change deriv (fun s => Real.cos (freq * s - beta * z)) t = _ at hd
  rw [hd]
  ring

private lemma deriv_partialTime_cos_mode (freq beta t z : ℝ) :
    deriv (fun s => partialTime (fun t z => Real.cos (freq * t - beta * z)) s z) t =
      -(freq ^ 2) * Real.cos (freq * t - beta * z) := by
  have hfun : (fun s => partialTime (fun t z => Real.cos (freq * t - beta * z)) s z) =
      fun s => -freq * Real.sin (freq * s - beta * z) :=
    funext fun s => partialTime_cos_mode freq beta s z
  rw [hfun]
  have hinner : HasDerivAt (fun s => freq * s - beta * z) freq t := by
    simpa using ((hasDerivAt_id t).const_mul freq).sub_const (beta * z)
  have h := ((Real.hasDerivAt_sin (freq * t - beta * z)).comp t hinner).const_mul (-freq)
  have hd := h.deriv
  change deriv (fun s => -freq * Real.sin (freq * s - beta * z)) t = _ at hd
  rw [hd]
  ring

private lemma partialZ_cos_mode (freq beta t z : ℝ) :
    partialZ (fun t z => Real.cos (freq * t - beta * z)) t z =
      beta * Real.sin (freq * t - beta * z) := by
  unfold partialZ
  show deriv (fun w => Real.cos (freq * t - beta * w)) z =
    beta * Real.sin (freq * t - beta * z)
  have hinner : HasDerivAt (fun w => freq * t - beta * w) (-beta) z := by
    simpa using ((hasDerivAt_id z).const_mul beta).const_sub (freq * t)
  have h := (Real.hasDerivAt_cos (freq * t - beta * z)).comp z hinner
  have hd := h.deriv
  change deriv (fun w => Real.cos (freq * t - beta * w)) z = _ at hd
  rw [hd]
  ring

private lemma deriv_partialZ_cos_mode (freq beta t z : ℝ) :
    deriv (fun w => partialZ (fun t z => Real.cos (freq * t - beta * z)) t w) z =
      -(beta ^ 2) * Real.cos (freq * t - beta * z) := by
  have hfun : (fun w => partialZ (fun t z => Real.cos (freq * t - beta * z)) t w) =
      fun w => beta * Real.sin (freq * t - beta * w) :=
    funext fun w => partialZ_cos_mode freq beta t w
  rw [hfun]
  have hinner : HasDerivAt (fun w => freq * t - beta * w) (-beta) z := by
    simpa using ((hasDerivAt_id z).const_mul beta).const_sub (freq * t)
  have h := ((Real.hasDerivAt_sin (freq * t - beta * z)).comp z hinner).const_mul beta
  have hd := h.deriv
  change deriv (fun w => beta * Real.sin (freq * t - beta * w)) z = _ at hd
  rw [hd]
  ring

private lemma partialTime_evanescent_mode (freq alpha t z : ℝ) :
    partialTime (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) t z =
      -freq * Real.sin (freq * t) * Real.exp (-alpha * z) := by
  unfold partialTime
  show deriv (fun s => Real.cos (freq * s) * Real.exp (-alpha * z)) t =
    -freq * Real.sin (freq * t) * Real.exp (-alpha * z)
  have hinner : HasDerivAt (fun s => freq * s) freq t := by
    simpa using (hasDerivAt_id t).const_mul freq
  have h := ((Real.hasDerivAt_cos (freq * t)).comp t hinner).mul_const
    (Real.exp (-alpha * z))
  have hd := h.deriv
  change deriv (fun s => Real.cos (freq * s) * Real.exp (-alpha * z)) t = _ at hd
  rw [hd]
  ring

private lemma deriv_partialTime_evanescent_mode (freq alpha t z : ℝ) :
    deriv (fun s => partialTime
      (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) s z) t =
      -(freq ^ 2) * (Real.cos (freq * t) * Real.exp (-alpha * z)) := by
  have hfun : (fun s => partialTime
      (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) s z) =
      fun s => -freq * Real.sin (freq * s) * Real.exp (-alpha * z) :=
    funext fun s => partialTime_evanescent_mode freq alpha s z
  rw [hfun]
  have hinner : HasDerivAt (fun s => freq * s) freq t := by
    simpa using (hasDerivAt_id t).const_mul freq
  have h := (((Real.hasDerivAt_sin (freq * t)).comp t hinner).const_mul
    (-freq)).mul_const (Real.exp (-alpha * z))
  have hd := h.deriv
  change deriv (fun s => -freq * Real.sin (freq * s) * Real.exp (-alpha * z)) t = _ at hd
  rw [hd]
  ring

private lemma partialZ_evanescent_mode (freq alpha t z : ℝ) :
    partialZ (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) t z =
      -alpha * (Real.cos (freq * t) * Real.exp (-alpha * z)) := by
  unfold partialZ
  show deriv (fun w => Real.cos (freq * t) * Real.exp (-alpha * w)) z =
    -alpha * (Real.cos (freq * t) * Real.exp (-alpha * z))
  have hinner : HasDerivAt (fun w => -alpha * w) (-alpha) z := by
    simpa using (hasDerivAt_id z).const_mul (-alpha)
  have h := ((Real.hasDerivAt_exp (-alpha * z)).comp z hinner).const_mul
    (Real.cos (freq * t))
  have hd := h.deriv
  change deriv (fun w => Real.cos (freq * t) * Real.exp (-alpha * w)) z = _ at hd
  rw [hd]
  ring

private lemma deriv_partialZ_evanescent_mode (freq alpha t z : ℝ) :
    deriv (fun w => partialZ
      (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) t w) z =
      alpha ^ 2 * (Real.cos (freq * t) * Real.exp (-alpha * z)) := by
  have hfun : (fun w => partialZ
      (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) t w) =
      fun w => -alpha * (Real.cos (freq * t) * Real.exp (-alpha * w)) :=
    funext fun w => partialZ_evanescent_mode freq alpha t w
  rw [hfun]
  have hinner : HasDerivAt (fun w => -alpha * w) (-alpha) z := by
    simpa using (hasDerivAt_id z).const_mul (-alpha)
  have h := (((Real.hasDerivAt_exp (-alpha * z)).comp z hinner).const_mul
    (Real.cos (freq * t))).const_mul (-alpha)
  have hd := h.deriv
  change deriv (fun w => -alpha * (Real.cos (freq * t) * Real.exp (-alpha * w))) z = _ at hd
  rw [hd]
  ring

/-- Sinusoidal profile and travelling cosine mode satisfy the
scalar equations exactly under the dispersion relation
`freq^2 = c0^2 (beta^2 + kc^2)`. -/
theorem propagatingMode_satisfies_scalarEquations (kc beta freq c0 : ℝ) :
    profileEquation (fun x => Real.sin (kc * x)) kc ∧
      modeEquation c0 kc (fun t z => Real.cos (freq * t - beta * z)) ↔
        freq ^ 2 = c0 ^ 2 * (beta ^ 2 + kc ^ 2) := by
  constructor
  · intro h
    obtain ⟨_, hmode⟩ := h
    have h00 := hmode 0 0
    rw [deriv_partialTime_cos_mode, deriv_partialZ_cos_mode] at h00
    simp at h00
    linear_combination -h00
  · intro hdisp
    refine ⟨sin_profileEquation kc, ?_⟩
    intro t z
    show deriv (fun s => partialTime (fun t z => Real.cos (freq * t - beta * z)) s z) t =
      c0 ^ 2 * (deriv (fun w => partialZ (fun t z => Real.cos (freq * t - beta * z)) t w) z -
        kc ^ 2 * Real.cos (freq * t - beta * z))
    rw [deriv_partialTime_cos_mode, deriv_partialZ_cos_mode, hdisp]
    ring

/-- Propagating instance of the source-free Maxwell result. -/
theorem propagatingMode_sourceFreeVacuumMaxwell (kc beta freq : ℝ) (c : SpeedOfLight)
    (hdisp : freq ^ 2 = (c : ℝ) ^ 2 * (beta ^ 2 + kc ^ 2)) :
    sourceFreeVacuumMaxwell c
      (separableElectricField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t - beta * z)))
      (separableMagneticField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t - beta * z))) := by
  obtain ⟨hprof, hmode⟩ :=
    (propagatingMode_satisfies_scalarEquations kc beta freq c).mpr hdisp
  exact separableFields_sourceFreeVacuumMaxwell _ _ kc c (by fun_prop) (by
    have hcd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.cos (freq * p.1 - beta * p.2)) := by
      fun_prop
    exact hcd) hprof hmode

/-- Sinusoidal profile and the exponential mode
`cos (freq t) exp (-alpha z)` satisfy the mode equation exactly
under `freq^2 = c0^2 (kc^2 - alpha^2)`. No sign is imposed on
`alpha`: the mode is evanescent (decaying along the guide) exactly
when `0 < alpha`, see `evanescentMode_decay`; `alpha = 0` gives a
mode independent of `z` and `alpha < 0` a growing one. -/
theorem evanescentMode_satisfies_modeEquation (kc alpha freq c0 : ℝ) :
    modeEquation c0 kc (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) ↔
      freq ^ 2 = c0 ^ 2 * (kc ^ 2 - alpha ^ 2) := by
  constructor
  · intro hmode
    have h00 := hmode 0 0
    rw [deriv_partialTime_evanescent_mode, deriv_partialZ_evanescent_mode] at h00
    simp at h00
    linear_combination -h00
  · intro hdisp t z
    show deriv (fun s => partialTime
        (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) s z) t =
      c0 ^ 2 * (deriv (fun w => partialZ
          (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)) t w) z -
        kc ^ 2 * (Real.cos (freq * t) * Real.exp (-alpha * z)))
    rw [deriv_partialTime_evanescent_mode, deriv_partialZ_evanescent_mode, hdisp]
    ring

/-- Exponential-mode instance of the source-free Maxwell result.
It holds for every real `alpha`; the mode is evanescent when
`0 < alpha`, see `evanescentMode_decay`. -/
theorem evanescentMode_sourceFreeVacuumMaxwell (kc alpha freq : ℝ) (c : SpeedOfLight)
    (hdisp : freq ^ 2 = (c : ℝ) ^ 2 * (kc ^ 2 - alpha ^ 2)) :
    sourceFreeVacuumMaxwell c
      (separableElectricField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)))
      (separableMagneticField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z))) := by
  have hmode := (evanescentMode_satisfies_modeEquation kc alpha freq c).mpr hdisp
  exact separableFields_sourceFreeVacuumMaxwell _ _ kc c (by fun_prop) (by
    have hcd : ContDiff ℝ ∞
        (fun p : ℝ × ℝ => Real.cos (freq * p.1) * Real.exp (-alpha * p.2)) := by
      fun_prop
    exact hcd) (sin_profileEquation kc) hmode

/-- **Evanescence for positive attenuation.** When `0 < alpha` the
amplitude `exp (-alpha z)` of the exponential mode is strictly
decreasing along the guide, and at every time the mode
`cos (freq t) exp (-alpha z)` tends to zero as `z → ∞`. -/
theorem evanescentMode_decay (alpha freq : ℝ) (halpha : 0 < alpha) :
    StrictAnti (fun z : ℝ => Real.exp (-alpha * z)) ∧
      ∀ t : ℝ, Filter.Tendsto (fun z => Real.cos (freq * t) * Real.exp (-alpha * z))
        Filter.atTop (nhds 0) := by
  refine ⟨fun z w hzw => ?_, fun t => ?_⟩
  · exact Real.exp_lt_exp.mpr (by nlinarith)
  · have hlin : Filter.Tendsto (fun z : ℝ => alpha * z) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop halpha
    have hexp : Filter.Tendsto (fun z : ℝ => Real.exp (-alpha * z)) Filter.atTop (nhds 0) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).congr fun z => by
        simp [Function.comp, neg_mul]
    have hmul := hexp.const_mul (Real.cos (freq * t))
    rwa [mul_zero] at hmul

end PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
