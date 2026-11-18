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
equation `f_tt = c0^2 (f_zz - kc^2 f)`, the fields satisfy the
source-free vacuum Maxwell equations at speed `c0`, and the
separable guide potential is an extremum of the free-space
Lagrangian with zero current at the associated speed of light.

## ii. Key results

- `separableFields_sourceFreeVacuumMaxwell`: the separable
  fields satisfy the source-free vacuum Maxwell equations.
- `separableFields_isExtrema_withFreeSpace`: the extremum
  form at the free-space speed of light.
- `propagatingMode_sourceFreeVacuumMaxwell` and
  `evanescentMode_sourceFreeVacuumMaxwell`: concrete
  propagating and evanescent modes.

## iii. Table of contents

- A. Partial derivatives and the scalar equations
- B. Separable fields and elementary Maxwell operators
- C. Source-free vacuum Maxwell equations
- D. Extremum form with free-space constants
- E. Failure of the mode equation and concrete modes

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

/-- Source-free vacuum Maxwell equations at speed `c0`. -/
def sourceFreeVacuumMaxwell (c0 : ℝ) (E B : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ) : Prop :=
  ∀ t x y z : ℝ, spaceDivergence E t x y z = 0 ∧ spaceDivergence B t x y z = 0 ∧
    spaceCurl E t x y z = ![-(timeDerivativeComponent B t x y z 0),
      -(timeDerivativeComponent B t x y z 1), -(timeDerivativeComponent B t x y z 2)] ∧
    spaceCurl B t x y z = ![(c0 ^ 2)⁻¹ * timeDerivativeComponent E t x y z 0,
      (c0 ^ 2)⁻¹ * timeDerivativeComponent E t x y z 1,
      (c0 ^ 2)⁻¹ * timeDerivativeComponent E t x y z 2]

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

private lemma differentiableAt_partialTime_right (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    DifferentiableAt ℝ (fun w => partialTime f t w) z := by
  have hfun : (fun w => partialTime f t w) =
      (fun w => fderiv ℝ (Function.uncurry f) (t, w) (1, 0)) :=
    funext fun w => partialTime_eq_fderiv f hf t w
  rw [hfun]
  exact (differentiable_fderiv_apply f hf (1, 0) (t, z)).comp z
    ((differentiableAt_const t).prodMk (differentiableAt_id))

private lemma differentiableAt_partialZ_left (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    DifferentiableAt ℝ (fun s => partialZ f s z) t := by
  have hfun : (fun s => partialZ f s z) =
      (fun p => fderiv ℝ (Function.uncurry f) p (0, 1)) ∘ (fun s => (s, z)) :=
    funext fun s => partialZ_eq_fderiv f hf s z
  rw [hfun]
  exact (differentiable_fderiv_apply f hf (0, 1) (t, z)).comp t
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

private lemma differentiableAt_f_left (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    DifferentiableAt ℝ (fun s => f s z) t := by
  have h1 : Differentiable ℝ (Function.uncurry f) := hf.differentiable (by norm_num)
  have hfun : (fun s => f s z) = (Function.uncurry f) ∘ (fun s => (s, z)) := rfl
  rw [hfun]
  exact (h1 (t, z)).comp t ((differentiableAt_id).prodMk (differentiableAt_const z))

private lemma differentiableAt_f_right (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t z : ℝ) :
    DifferentiableAt ℝ (f t) z := by
  have h1 : Differentiable ℝ (Function.uncurry f) := hf.differentiable (by norm_num)
  have hfun : (f t) = (Function.uncurry f) ∘ (fun w => (t, w)) := rfl
  rw [hfun]
  exact (h1 (t, z)).comp z ((differentiableAt_const t).prodMk (differentiableAt_id))

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

/-- Gauss's law for the separable electric field. -/
theorem separable_divergence_electric (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc c0 : ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation c0 kc f) :
    ∀ t x y z : ℝ, spaceDivergence (separableElectricField a f) t x y z = 0 := by
  intro t x y z
  simp [spaceDivergence, separableElectricField]

/-- Gauss's law for the separable magnetic field. -/
theorem separable_divergence_magnetic (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc c0 : ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation c0 kc f) :
    ∀ t x y z : ℝ, spaceDivergence (separableMagneticField a f) t x y z = 0 := by
  intro t x y z
  have ha_diff : Differentiable ℝ a := ha.differentiable (by norm_num)
  have h1 : deriv (fun u => separableMagneticField a f t u y z 0) x =
      -(deriv a x * partialZ f t z) := by
    have hfun : (fun u => separableMagneticField a f t u y z 0) =
        (fun u => -(a u * partialZ f t z)) := by
      funext u; simp [separableMagneticField]
    rw [hfun]
    exact (((ha_diff x).hasDerivAt.mul_const _).neg).deriv
  have h2 : deriv (fun v => separableMagneticField a f t x v z 1) y = 0 := by
    simp [separableMagneticField]
  have h3 : deriv (fun w => separableMagneticField a f t x y w 2) z =
      deriv a x * partialZ f t z := by
    have hfun : (fun w => separableMagneticField a f t x y w 2) =
        (fun w => deriv a x * f t w) := by
      funext w; simp [separableMagneticField]
    rw [hfun]
    exact ((differentiableAt_f_right f hf t z).hasDerivAt.const_mul _).deriv
  simp [spaceDivergence, h1, h2, h3]

/-- Faraday's law for the separable fields. -/
theorem separable_faraday (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc c0 : ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation c0 kc f) :
    ∀ t x y z : ℝ, spaceCurl (separableElectricField a f) t x y z =
      ![-(timeDerivativeComponent (separableMagneticField a f) t x y z 0),
        -(timeDerivativeComponent (separableMagneticField a f) t x y z 1),
        -(timeDerivativeComponent (separableMagneticField a f) t x y z 2)] := by
  intro t x y z
  have ha_diff : Differentiable ℝ a := ha.differentiable (by norm_num)
  have dE_y2 : deriv (fun v => separableElectricField a f t x v z 2) y = 0 := by
    simp [separableElectricField]
  have dE_z1 : deriv (fun w => separableElectricField a f t x y w 1) z =
      -(a x * deriv (fun w => partialTime f t w) z) := by
    have hfun : (fun w => separableElectricField a f t x y w 1) =
        (fun w => -(a x * partialTime f t w)) := by
      funext w; simp [separableElectricField]
    rw [hfun]
    exact ((differentiableAt_partialTime_right f hf t z).hasDerivAt.const_mul (a x)).neg.deriv
  have dE_x1 : deriv (fun u => separableElectricField a f t u y z 1) x =
      -(deriv a x * partialTime f t z) := by
    have hfun : (fun u => separableElectricField a f t u y z 1) =
        (fun u => -(a u * partialTime f t z)) := by
      funext u; simp [separableElectricField]
    rw [hfun]
    exact (((ha_diff x).hasDerivAt.mul_const _).neg).deriv
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
    rw [hfun]
    exact ((differentiableAt_partialZ_left f hf t z).hasDerivAt.const_mul (a x)).neg.deriv
  have dB_t1 : deriv (fun s => separableMagneticField a f s x y z 1) t = 0 := by
    simp [separableMagneticField]
  have dB_t2 : deriv (fun s => separableMagneticField a f s x y z 2) t =
      deriv a x * partialTime f t z := by
    have hfun : (fun s => separableMagneticField a f s x y z 2) =
        (fun s => deriv a x * f s z) := by
      funext s; simp [separableMagneticField]
    rw [hfun]
    exact ((differentiableAt_f_left f hf t z).hasDerivAt.const_mul _).deriv
  have hmix := mixed_partial_eq f hf t z
  ext i
  fin_cases i <;>
    simp [spaceCurl, timeDerivativeComponent, dE_y2, dE_z1, dE_x1, dE_y0, dE_z0, dE_x2,
      dB_t0, dB_t1, dB_t2, hmix]

/-- Ampère's law for the separable fields; both scalar equations
are used here. -/
theorem separable_ampere (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc c0 : ℝ) (hc0 : 0 < c0)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation c0 kc f) :
    ∀ t x y z : ℝ, spaceCurl (separableMagneticField a f) t x y z =
      ![(c0 ^ 2)⁻¹ * timeDerivativeComponent (separableElectricField a f) t x y z 0,
        (c0 ^ 2)⁻¹ * timeDerivativeComponent (separableElectricField a f) t x y z 1,
        (c0 ^ 2)⁻¹ * timeDerivativeComponent (separableElectricField a f) t x y z 2] := by
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
    have hc : (c0 ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt hc0)
    field_simp
    ring
  · simp [spaceCurl, timeDerivativeComponent, dB_x1, dB_y0, dE_t2]

/-- **Source-free vacuum Maxwell equations for the separable
fields.** -/
theorem separableFields_sourceFreeVacuumMaxwell (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc c0 : ℝ)
    (hc0 : 0 < c0) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (hmode : modeEquation c0 kc f) :
    sourceFreeVacuumMaxwell c0 (separableElectricField a f) (separableMagneticField a f) := by
  intro t x y z
  exact ⟨separable_divergence_electric a f kc c0 ha hf hprofile hmode t x y z,
    separable_divergence_magnetic a f kc c0 ha hf hprofile hmode t x y z,
    separable_faraday a f kc c0 ha hf hprofile hmode t x y z,
    separable_ampere a f kc c0 hc0 ha hf hprofile hmode t x y z⟩

/-! ## D. Extremum form with free-space constants -/

private lemma basis_apply (μ j : Fin 3) : (Space.basis μ : Space) j = if j = μ then 1 else 0 := by
  rw [← Space.basis.repr_symm_single]
  exact PiLp.single_apply (p := 2) (i := μ) (a := (1 : ℝ)) (j := j)

/-- Coordinate projection on `Space`. -/
private noncomputable def coord (i : Fin 3) : Space →L[ℝ] ℝ :=
  LinearMap.mkContinuous ⟨⟨fun p => p i, fun _ _ => rfl⟩, fun _ _ => rfl⟩ 1 fun p => by
    rw [one_mul]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => p j ^ 2)
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))

@[simp] private lemma coord_apply (i : Fin 3) (p : Space) : coord i p = p i := rfl

private lemma space_deriv_mul (a F : ℝ → ℝ) (p : Space) (ha : DifferentiableAt ℝ a (p 0))
    (hF : DifferentiableAt ℝ F (p 2)) (μ : Fin 3) :
    Space.deriv μ (fun q : Space => a (q 0) * F (q 2)) p =
      a (p 0) * (deriv F (p 2) * if 2 = μ then 1 else 0) +
        F (p 2) * (deriv a (p 0) * if 0 = μ then 1 else 0) := by
  have h : HasFDerivAt (fun q : Space => a (q 0) * F (q 2)) _ p :=
    (ha.hasDerivAt.comp_hasFDerivAt p (coord 0).hasFDerivAt).mul
      (hF.hasDerivAt.comp_hasFDerivAt p (coord 2).hasFDerivAt)
  simp [Space.deriv, h.fderiv, basis_apply]

/-- **Extremum form with the free-space constants.** The fields
satisfy the source-free equations at the associated speed, the
separable potential is an extremum with zero current, and the
potential and zero current are smooth. -/
theorem separableFields_isExtrema_withFreeSpace
    (𝓕 : FreeSpace) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc : ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc)
    (hmode : modeEquation ((𝓕.c : ℝ)) kc f) :
    sourceFreeVacuumMaxwell ((𝓕.c : ℝ))
        (separableElectricField a f) (separableMagneticField a f) ∧
      (separableGuidePotential
        𝓕.c a f).IsExtrema 𝓕 0 ∧
      ContDiff ℝ ∞ (separableGuidePotential
        𝓕.c a f) ∧
      ContDiff ℝ ∞ (0 : LorentzCurrentDensity) := by
  have hA : ContDiff ℝ ∞
      (separableGuidePotential 𝓕.c a f) :=
    contDiff_separableGuidePotential
      𝓕.c a f ha hf
  have hJ0 : ContDiff ℝ ∞ (0 : LorentzCurrentDensity) := contDiff_zero_fun
  have hExt :
      (separableGuidePotential
        𝓕.c a f).IsExtrema 𝓕 0 := by
    rw [ElectromagneticPotential.isExtrema_iff_gauss_ampere_magneticFieldMatrix hA 0 hJ0]
    obtain ⟨hE, hB, -⟩ :=
      separableGuidePotential_fields
        𝓕.c a f ha hf
    have hEc : ∀ (s : Time) (q : Space) (i : Fin 3),
        (separableGuidePotential
          𝓕.c a f).electricField 𝓕.c s q i =
          separableElectricField a f s.val (q 0) (q 1) (q 2) i := by
      intro s q i
      rw [hE s q]
      fin_cases i <;> simp [separableElectricField, partialTime]
    have hBc : ∀ (s : Time) (q : Space) (i : Fin 3),
        (separableGuidePotential
          𝓕.c a f).magneticField 𝓕.c s q i =
          separableMagneticField a f s.val (q 0) (q 1) (q 2) i := by
      intro s q i
      rw [hB s q]
      fin_cases i <;> simp [separableMagneticField, partialZ]
    have ha_diff : Differentiable ℝ a := ha.differentiable (by norm_num)
    have ha_deriv_diff : Differentiable ℝ (deriv a) :=
      (contDiff_infty_iff_deriv.mp ha).2.differentiable (by norm_num)
    intro t p
    refine ⟨?_, ?_⟩
    · simp only [LorentzCurrentDensity.chargeDensity_zero, Pi.zero_apply, zero_div]
      simp only [Space.div, Fin.sum_univ_three]
      have e0 : Space.deriv 0
          (fun q => (separableGuidePotential
            𝓕.c a f).electricField 𝓕.c t q 0) p = 0 := by
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c t q 0) = fun _ => 0 :=
          funext fun q => by rw [hEc t q 0]; simp [separableElectricField]
        rw [hfun]
        simp [Space.deriv]
      have e1 : Space.deriv 1
          (fun q => (separableGuidePotential
            𝓕.c a f).electricField 𝓕.c t q 1) p = 0 := by
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c t q 1) =
            (fun q => (fun u => -a u) (q 0) * (fun z => partialTime f t.val z) (q 2)) :=
          funext fun q => by
            rw [hEc t q 1]
            simp [separableElectricField]
        rw [hfun, space_deriv_mul (fun u => -a u) (fun z => partialTime f t.val z) p
          (ha_diff (p 0)).neg (differentiableAt_partialTime_right f hf t.val (p 2)) 1]
        simp
      have e2 : Space.deriv 2
          (fun q => (separableGuidePotential
            𝓕.c a f).electricField 𝓕.c t q 2) p = 0 := by
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c t q 2) = fun _ => 0 :=
          funext fun q => by rw [hEc t q 2]; simp [separableElectricField]
        rw [hfun]
        simp [Space.deriv]
      rw [e0, e1, e2]
      ring
    ·
      have hdiff_time : Differentiable ℝ
          ((separableGuidePotential 𝓕.c a f).electricField 𝓕.c · p) :=
        ElectromagneticPotential.electricField_differentiable_time (hA.of_le (by simp)) p
      have hsum : ∀ i : Fin 3, (∑ j, Space.deriv j
          ((separableGuidePotential 𝓕.c a f).magneticFieldMatrix 𝓕.c t · (j, i)) p) =
          (∇ ⨯ (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p i :=
        fun i => (ElectromagneticPotential.magneticField_curl_eq_magneticFieldMatrix
          (separableGuidePotential 𝓕.c a f) (hA.of_le (by simp)) t).symm
      have hda : deriv (fun u => -a u) (p 0) = -deriv a (p 0) :=
        ((ha_diff (p 0)).hasDerivAt.neg).deriv
      have dB0_1 : Space.deriv 1
          (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 0) p = 0 := by
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 0) =
            (fun q => (fun u => -a u) (q 0) * (fun z => partialZ f t.val z) (q 2)) :=
          funext fun q => by
            rw [hBc t q 0]
            simp [separableMagneticField]
        rw [hfun, space_deriv_mul (fun u => -a u) (fun z => partialZ f t.val z) p
          (ha_diff (p 0)).neg (differentiableAt_partialZ_right f hf t.val (p 2)) 1, hda]
        simp
      have dB0_2 : Space.deriv 2
          (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 0) p =
          -a (p 0) * deriv (fun w => partialZ f t.val w) (p 2) := by
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 0) =
            (fun q => (fun u => -a u) (q 0) * (fun z => partialZ f t.val z) (q 2)) :=
          funext fun q => by
            rw [hBc t q 0]
            simp [separableMagneticField]
        rw [hfun, space_deriv_mul (fun u => -a u) (fun z => partialZ f t.val z) p
          (ha_diff (p 0)).neg (differentiableAt_partialZ_right f hf t.val (p 2)) 2, hda]
        simp
      have dB1 : ∀ μ : Fin 3, Space.deriv μ
          (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 1) p = 0 := by
        intro μ
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 1) =
            fun _ => 0 :=
          funext fun q => by rw [hBc t q 1]; simp [separableMagneticField]
        rw [hfun]
        simp [Space.deriv]
      have dB2_0 : Space.deriv 0
          (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 2) p =
          f t.val (p 2) * deriv (deriv a) (p 0) := by
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 2) =
            (fun q => deriv a (q 0) * f t.val (q 2)) :=
          funext fun q => by rw [hBc t q 2]; simp [separableMagneticField]
        rw [hfun, space_deriv_mul (deriv a) (fun z => f t.val z) p
          (ha_deriv_diff (p 0)) (differentiableAt_f_right f hf t.val (p 2)) 0]
        simp
      have dB2_1 : Space.deriv 1
          (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 2) p = 0 := by
        have hfun : (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 2) =
            (fun q => deriv a (q 0) * f t.val (q 2)) :=
          funext fun q => by rw [hBc t q 2]; simp [separableMagneticField]
        rw [hfun, space_deriv_mul (deriv a) (fun z => f t.val z) p
          (ha_deriv_diff (p 0)) (differentiableAt_f_right f hf t.val (p 2)) 1]
        simp
      intro i
      have key : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
      rcases key i with rfl | rfl | rfl
      · simp only [LorentzCurrentDensity.currentDensity_zero, Pi.zero_apply, PiLp.zero_apply, mul_zero, sub_zero]
        rw [hsum 0, ← Time.deriv_euclid hdiff_time t]
        have ht : Time.deriv
            (fun s => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c s p 0) t = 0 := by
          have hfun : (fun s => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c s p 0) =
              fun _ => 0 :=
            funext fun s => by rw [hEc s p 0]; simp [separableElectricField]
          rw [hfun]
          simp [Time.deriv]
        have hc : (∇ ⨯ (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p 0 = 0 := by
          have hcurl : (∇ ⨯ (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p 0 =
              Space.deriv 1 (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 2) p -
              Space.deriv 2 (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 1) p := by
            simp [Space.curl]
          rw [hcurl, dB2_1, dB1 2]
          simp
        rw [ht, hc]
        ring
      · simp only [LorentzCurrentDensity.currentDensity_zero, Pi.zero_apply, PiLp.zero_apply, mul_zero, sub_zero]
        rw [hsum 1, ← Time.deriv_euclid hdiff_time t]
        have ht : Time.deriv
            (fun s => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c s p 1) t =
            -(a (p 0) * deriv (fun s => partialTime f s (p 2)) t.val) := by
          apply Time.deriv_eq_of_hasDerivAt
            (f := fun s => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c s p 1)
          have hcomp : (fun τ : ℝ => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c ⟨τ⟩ p 1) =
              (fun τ => -(a (p 0) * partialTime f τ (p 2))) :=
            funext fun τ => by rw [hEc ⟨τ⟩ p 1]; simp [separableElectricField]
          rw [hcomp]
          exact ((differentiableAt_partialTime_left f hf t.val (p 2)).hasDerivAt.const_mul
            (a (p 0))).neg
        have hc : (∇ ⨯ (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p 1 =
            -(a (p 0) * deriv (fun w => partialZ f t.val w) (p 2)) -
              f t.val (p 2) * deriv (deriv a) (p 0) := by
          have hcurl : (∇ ⨯ (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p 1 =
              Space.deriv 2 (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 0) p -
              Space.deriv 0 (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 2) p := by
            simp [Space.curl]
          rw [hcurl, dB0_2, dB2_0]
          ring
        have hμε : 𝓕.μ₀ * 𝓕.ε₀ = ((𝓕.c : ℝ) ^ 2)⁻¹ := by
          rw [FreeSpace.c_sq]
          simp [mul_comm]
        rw [ht, hc, hμε, hmode t.val (p 2), hprofile (p 0)]
        have hcne : (𝓕.c : ℝ) ≠ 0 := ne_of_gt 𝓕.c.pos
        field_simp
        ring
      · simp only [LorentzCurrentDensity.currentDensity_zero, Pi.zero_apply, PiLp.zero_apply, mul_zero, sub_zero]
        rw [hsum 2, ← Time.deriv_euclid hdiff_time t]
        have ht : Time.deriv
            (fun s => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c s p 2) t = 0 := by
          have hfun : (fun s => (separableGuidePotential 𝓕.c a f).electricField 𝓕.c s p 2) =
              fun _ => 0 :=
            funext fun s => by rw [hEc s p 2]; simp [separableElectricField]
          rw [hfun]
          simp [Time.deriv]
        have hc : (∇ ⨯ (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p 2 = 0 := by
          have hcurl : (∇ ⨯ (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t) p 2 =
              Space.deriv 0 (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 1) p -
              Space.deriv 1 (fun q => (separableGuidePotential 𝓕.c a f).magneticField 𝓕.c t q 0) p := by
            simp [Space.curl]
          rw [hcurl, dB1 0, dB0_1]
          simp
        rw [ht, hc]
        ring
  exact ⟨separableFields_sourceFreeVacuumMaxwell a f kc (𝓕.c : ℝ) 𝓕.c.pos ha hf
    hprofile hmode, hExt, hA, hJ0⟩

/-! ## E. Failure of the mode equation and concrete modes -/

/-- A dispersion mismatch at a point where `a` is nonzero breaks
the source-free Maxwell equations: the Ampère residual is
nonzero. -/
theorem not_sourceFree_of_modeEquation_failure (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (kc c0 : ℝ)
    (hc0 : 0 < c0) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hprofile : profileEquation a kc) (t x z : ℝ) (hax : a x ≠ 0)
    (hmismatch : deriv (fun s => partialTime f s z) t ≠
      c0 ^ 2 * (deriv (fun w => partialZ f t w) z - kc ^ 2 * f t z)) :
    ¬ sourceFreeVacuumMaxwell c0 (separableElectricField a f) (separableMagneticField a f) := by
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
  have hc : (c0 ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt hc0)
  have h2 := congrArg (fun r => -(c0 ^ 2) * r) hcomp
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
theorem propagatingMode_sourceFreeVacuumMaxwell (kc beta freq c0 : ℝ) (hc0 : 0 < c0)
    (hdisp : freq ^ 2 = c0 ^ 2 * (beta ^ 2 + kc ^ 2)) :
    sourceFreeVacuumMaxwell c0
      (separableElectricField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t - beta * z)))
      (separableMagneticField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t - beta * z))) := by
  obtain ⟨hprof, hmode⟩ :=
    (propagatingMode_satisfies_scalarEquations kc beta freq c0).mpr hdisp
  exact separableFields_sourceFreeVacuumMaxwell _ _ kc c0 hc0 (by fun_prop) (by
    have hcd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.cos (freq * p.1 - beta * p.2)) := by
      fun_prop
    exact hcd) hprof hmode

/-- Sinusoidal profile and decaying oscillating mode satisfy the
mode equation exactly under `freq^2 = c0^2 (kc^2 - alpha^2)`. -/
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

/-- Evanescent instance of the source-free Maxwell result. -/
theorem evanescentMode_sourceFreeVacuumMaxwell (kc alpha freq c0 : ℝ) (hc0 : 0 < c0)
    (hdisp : freq ^ 2 = c0 ^ 2 * (kc ^ 2 - alpha ^ 2)) :
    sourceFreeVacuumMaxwell c0
      (separableElectricField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z)))
      (separableMagneticField (fun x => Real.sin (kc * x)) (fun t z => Real.cos (freq * t) * Real.exp (-alpha * z))) := by
  have hmode := (evanescentMode_satisfies_modeEquation kc alpha freq c0).mpr hdisp
  exact separableFields_sourceFreeVacuumMaxwell _ _ kc c0 hc0 (by fun_prop) (by
    have hcd : ContDiff ℝ ∞
        (fun p : ℝ × ℝ => Real.cos (freq * p.1) * Real.exp (-alpha * p.2)) := by
      fun_prop
    exact hcd) (sin_profileEquation kc) hmode

end PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
