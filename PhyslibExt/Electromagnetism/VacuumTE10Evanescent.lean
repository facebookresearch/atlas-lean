/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.RectangularPECTraces
public import PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Evanescent TE10 field of a rectangular guide below cutoff

The TE10 field of a hollow rectangular guide driven below its cutoff frequency, as a separable
vacuum Maxwell field that decays exponentially along the guide.

## i. Overview

Let `a > 0` be the guide width along `x`, `b > 0` its height along `y`, `kc = π / a` the TE10
cutoff wavenumber, `c` the speed of light, `E0 ≠ 0` an amplitude and `0 < ω < c kc` a frequency
strictly below cutoff. The decay rate `κ = sqrt (kc^2 - ω^2 / c^2)` is then positive. The
evanescent field is the separable field with transverse profile `sin (kc x)` and longitudinal
mode `f(t, z) = -(E0 / ω) exp (-κ z) sin (ω t)`, whose components are
`E = (0, E0 sin (kc x) exp (-κ z) cos (ω t), 0)` and
`B = (-(κ E0 / ω) sin (kc x) exp (-κ z) sin (ω t), 0,`
`-(kc E0 / ω) cos (kc x) exp (-κ z) sin (ω t))`.

These fields satisfy the source-free vacuum Maxwell equations at every time and point, through
the general theorem for separable fields, and at every time they satisfy the perfect-conductor
traces on the four side walls `x = 0, a`, `y = 0, b`. For `E0 ≠ 0` the electric field is not
identically zero, with `E_y = E0` at `x = a / 2`, `t = z = 0`. On the half-guide `z ≥ 0` every
electric component is bounded by `|E0| exp (-κ z)` and every magnetic component by
`((κ + kc) |E0| / ω) exp (-κ z)`, and every component tends to zero as `z → ∞`.

Decay is claimed only toward positive `z`: the smooth extension of the field to all `z` is
unbounded as `z → -∞`, and no finite-energy statement over the whole guide is made. At the
cutoff `ω = c kc` the decay rate is zero, and no statement divides by `κ`. The field
definitions take the rate `κ` as a parameter, and a rate violating `ω^2 = c^2 (kc^2 - κ^2)`
breaks the Maxwell equations.

## ii. Key results

- `decayRate_pos`, `decayRate_sq` and `decayRate_at_cutoff`: the decay rate below and at cutoff.
- `evanescent_sourceFreeVacuumMaxwell`: the evanescent fields satisfy the source-free vacuum
  Maxwell equations.
- `not_evanescent_sourceFreeVacuumMaxwell_of_wrong_rate`: a wrong decay rate breaks them.
- `evanescent_rectangularGuidePECTraces`: the PEC traces on the four side walls at every time.
- `evanescentElectricField_center` and `evanescentElectricField_ne_zero`: the field is nonzero.
- `evanescentFields_abs_le` and `tendsto_evanescentFields_atTop`: exponential decay toward
  positive `z`.
- `not_bddAbove_evanescentElectricField_nonpos`: no decay toward negative `z`.
- `te10Evanescent_correct`: the combined statement.

## iii. Table of contents

- A. The evanescent TE10 field
- B. Auxiliary computations
- C. The decay rate
- D. Scalar equations and regularity
- E. Field components
- F. Bulk equations
- G. Side-wall traces
- H. Nonvanishing
- I. Decay toward positive `z`
- J. Main result

## iv. References

- D. M. Pozar, *Microwave Engineering*, fourth edition, Wiley, 2012, Sections 3.3 and 4.7: the
  TE10 mode of a rectangular waveguide, its cutoff frequency, and evanescent modes below cutoff.
- J. D. Jackson, *Classical Electrodynamics*, third edition, Wiley, 1998, Sections 8.3 and 8.4:
  boundary conditions at a perfect conductor and modes of a rectangular waveguide, including
  attenuation below the cutoff frequency.

-/

@[expose] public section

open scoped ContDiff
open Filter Topology

namespace PhyslibExt.Electromagnetism.VacuumTE10Evanescent

open PhyslibExt.Electromagnetism.RectangularPECTraces
open PhyslibExt.Electromagnetism.SeparableVacuumMaxwell

/-! ## A. The evanescent TE10 field -/

/-- The TE10 cutoff wavenumber `kc = π / a` of a guide of width `a`. -/
noncomputable def cutoffWavenumber (a : ℝ) : ℝ := Real.pi / a

/-- The TE10 transverse profile `sin (kc x)`. -/
noncomputable def te10Profile (a : ℝ) : ℝ → ℝ :=
  fun x => Real.sin (cutoffWavenumber a * x)

/-- The below-cutoff decay rate `κ = sqrt (kc^2 - ω^2 / c0^2)`. -/
noncomputable def decayRate (c0 a omega : ℝ) : ℝ :=
  Real.sqrt (cutoffWavenumber a ^ 2 - omega ^ 2 / c0 ^ 2)

/-- The evanescent longitudinal mode `f(t, z) = -(E0 / ω) exp (-κ z) sin (ω t)` with rate
`kappa`. -/
noncomputable def evanescentMode (E0 omega kappa : ℝ) : ℝ → ℝ → ℝ :=
  fun t z => -(E0 / omega) * Real.exp (-kappa * z) * Real.sin (omega * t)

/-- The evanescent electric field, the separable electric field of the TE10 profile and the
evanescent mode. -/
noncomputable def evanescentElectricField (a E0 omega kappa : ℝ) :
    ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  separableElectricField (te10Profile a) (evanescentMode E0 omega kappa)

/-- The evanescent magnetic field, the separable magnetic field of the TE10 profile and the
evanescent mode. -/
noncomputable def evanescentMagneticField (a E0 omega kappa : ℝ) :
    ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  separableMagneticField (te10Profile a) (evanescentMode E0 omega kappa)

/-- A field of time and three coordinates frozen at time `t`, as the point-to-vector map on
which the PEC trace predicates are stated. -/
def fieldAtTime (F : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ) (t : ℝ) : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  fun p => F t (p 0) (p 1) (p 2)

/-! ## B. Auxiliary computations -/

/-- Derivative of a constant multiple of the identity. -/
private lemma hasDerivAt_const_mul_id (c x : ℝ) :
    HasDerivAt (fun y : ℝ => c * y) c x := by
  simpa using (hasDerivAt_id x).const_mul c

/-- First derivative shape of the TE10 profile. -/
private lemma hasDerivAt_P1 (a x : ℝ) :
    HasDerivAt (te10Profile a)
      (Real.cos (cutoffWavenumber a * x) * cutoffWavenumber a) x := by
  unfold te10Profile
  exact (hasDerivAt_const_mul_id (cutoffWavenumber a) x).sin

/-- First derivative of the TE10 profile. -/
private lemma deriv_P1 (a x : ℝ) :
    deriv (te10Profile a) x
      = cutoffWavenumber a * Real.cos (cutoffWavenumber a * x) := by
  have h := (hasDerivAt_P1 a x).deriv
  rw [h]
  ring

/-- First derivative of the TE10 profile, as a function. -/
private lemma deriv_P1_fun (a : ℝ) :
    deriv (te10Profile a)
      = fun x => cutoffWavenumber a * Real.cos (cutoffWavenumber a * x) :=
  funext (deriv_P1 a)

/-- Second derivative shape of the TE10 profile. -/
private lemma hasDerivAt_P2 (a x : ℝ) :
    HasDerivAt (fun x => cutoffWavenumber a * Real.cos (cutoffWavenumber a * x))
      (cutoffWavenumber a * (-Real.sin (cutoffWavenumber a * x) * cutoffWavenumber a)) x :=
  ((hasDerivAt_const_mul_id (cutoffWavenumber a) x).cos).const_mul (cutoffWavenumber a)

/-- First time derivative shape of the evanescent mode. -/
private lemma hasDerivAt_T1 (E0 omega kappa t z : ℝ) :
    HasDerivAt (fun s => evanescentMode E0 omega kappa s z)
      (((-(E0 / omega)) * Real.exp (-kappa * z)) * (Real.cos (omega * t) * omega)) t := by
  simp only [evanescentMode]
  exact (hasDerivAt_const_mul_id omega t).sin.const_mul
    ((-(E0 / omega)) * Real.exp (-kappa * z))

/-- First time partial of the evanescent mode. -/
private lemma partialTime_eq (E0 omega kappa t z : ℝ) :
    partialTime (evanescentMode E0 omega kappa) t z
      = ((-(E0 / omega)) * Real.exp (-kappa * z)) * (omega * Real.cos (omega * t)) := by
  have h := (hasDerivAt_T1 E0 omega kappa t z).deriv
  unfold partialTime
  rw [h]
  ring

/-- Second time derivative shape of the evanescent mode. -/
private lemma hasDerivAt_T2 (E0 omega kappa t z : ℝ) :
    HasDerivAt
      (fun s => ((-(E0 / omega)) * Real.exp (-kappa * z)) * (omega * Real.cos (omega * s)))
      (((-(E0 / omega)) * Real.exp (-kappa * z)) * (omega * (-Real.sin (omega * t) * omega))) t :=
  (((hasDerivAt_const_mul_id omega t).cos).const_mul omega).const_mul
    ((-(E0 / omega)) * Real.exp (-kappa * z))

/-- Second time partial of the evanescent mode, factored. -/
private lemma deriv_T2_eq (E0 omega kappa t z : ℝ) :
    deriv (fun s => partialTime (evanescentMode E0 omega kappa) s z) t
      = (-((-(E0 / omega)) * Real.exp (-kappa * z) * Real.sin (omega * t))) * omega ^ 2 := by
  have hfun : (fun s => partialTime (evanescentMode E0 omega kappa) s z)
      = fun s => ((-(E0 / omega)) * Real.exp (-kappa * z)) * (omega * Real.cos (omega * s)) :=
    funext (fun s => partialTime_eq E0 omega kappa s z)
  rw [hfun]
  have h := (hasDerivAt_T2 E0 omega kappa t z).deriv
  rw [h]
  ring

/-- The mode at fixed time, rearranged as a constant times the exponential. -/
private lemma mode_funZ1_eq (E0 omega kappa t : ℝ) :
    (fun w => evanescentMode E0 omega kappa t w)
      = fun w => ((-(E0 / omega)) * Real.sin (omega * t)) * Real.exp (-kappa * w) := by
  funext w
  simp only [evanescentMode]
  ring

/-- First guide-coordinate derivative shape of the evanescent mode. -/
private lemma hasDerivAt_Z1 (E0 omega kappa t z : ℝ) :
    HasDerivAt (fun w => ((-(E0 / omega)) * Real.sin (omega * t)) * Real.exp (-kappa * w))
      (((-(E0 / omega)) * Real.sin (omega * t)) * (Real.exp (-kappa * z) * (-kappa))) z :=
  ((hasDerivAt_const_mul_id (-kappa) z).exp).const_mul
    ((-(E0 / omega)) * Real.sin (omega * t))

/-- First guide-coordinate partial of the evanescent mode. -/
private lemma partialZ_eq (E0 omega kappa t z : ℝ) :
    partialZ (evanescentMode E0 omega kappa) t z
      = ((-(E0 / omega)) * Real.sin (omega * t)) * (Real.exp (-kappa * z) * (-kappa)) := by
  have h : evanescentMode E0 omega kappa t
      = fun w => ((-(E0 / omega)) * Real.sin (omega * t)) * Real.exp (-kappa * w) :=
    mode_funZ1_eq E0 omega kappa t
  unfold partialZ
  rw [h]
  exact (hasDerivAt_Z1 E0 omega kappa t z).deriv

/-- The first guide-coordinate partial at fixed time, rearranged. -/
private lemma mode_funZ2_eq (E0 omega kappa t : ℝ) :
    (fun w => partialZ (evanescentMode E0 omega kappa) t w)
      = fun w => ((-(E0 / omega)) * Real.sin (omega * t)) * ((-kappa) * Real.exp (-kappa * w)) := by
  funext w
  rw [partialZ_eq]
  ring

/-- Second guide-coordinate derivative shape of the evanescent mode. -/
private lemma hasDerivAt_Z2 (E0 omega kappa t z : ℝ) :
    HasDerivAt
      (fun w => ((-(E0 / omega)) * Real.sin (omega * t)) * ((-kappa) * Real.exp (-kappa * w)))
      (((-(E0 / omega)) * Real.sin (omega * t)) *
        ((-kappa) * (Real.exp (-kappa * z) * (-kappa)))) z :=
  (((hasDerivAt_const_mul_id (-kappa) z).exp).const_mul (-kappa)).const_mul
    ((-(E0 / omega)) * Real.sin (omega * t))

/-- Second guide-coordinate partial of the evanescent mode, factored. -/
private lemma deriv_Z2_eq (E0 omega kappa t z : ℝ) :
    deriv (fun w => partialZ (evanescentMode E0 omega kappa) t w) z
      = ((-(E0 / omega)) * Real.exp (-kappa * z) * Real.sin (omega * t)) * kappa ^ 2 := by
  rw [mode_funZ2_eq]
  have h := (hasDerivAt_Z2 E0 omega kappa t z).deriv
  rw [h]
  ring

/-- The rate relation implies the mode equation, with no nonvanishing hypotheses. -/
private lemma modeEquation_of_rate_eq (c0 a E0 omega kappa : ℝ)
    (hrate : omega ^ 2 = c0 ^ 2 * (cutoffWavenumber a ^ 2 - kappa ^ 2)) :
    modeEquation c0 (cutoffWavenumber a) (evanescentMode E0 omega kappa) := by
  intro t z
  rw [deriv_T2_eq, deriv_Z2_eq]
  simp only [evanescentMode]
  have hG := congrArg
    (fun v => (-((-(E0 / omega)) * Real.exp (-kappa * z) * Real.sin (omega * t))) * v) hrate
  rw [hG]
  ring

/-- The time argument at which the mode attains a nonzero value. -/
private lemma harg_t0 (omega : ℝ) (homega : omega ≠ 0) :
    omega * ((Real.pi / 2) / omega) = Real.pi / 2 := by
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ homega

/-- The mode equation at the test point determines the rate relation. -/
private lemma rate_eq_of_point (c0 a E0 omega kappa : ℝ) (hE0 : E0 ≠ 0) (homega : omega ≠ 0)
    (hmode : deriv (fun s => partialTime (evanescentMode E0 omega kappa) s 0)
        ((Real.pi / 2) / omega)
      = c0 ^ 2 * (deriv (fun w => partialZ (evanescentMode E0 omega kappa)
          ((Real.pi / 2) / omega) w) 0
        - cutoffWavenumber a ^ 2 * evanescentMode E0 omega kappa ((Real.pi / 2) / omega) 0)) :
    omega ^ 2 = c0 ^ 2 * (cutoffWavenumber a ^ 2 - kappa ^ 2) := by
  have hM : -(E0 / omega) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hE0 homega)
  rw [deriv_T2_eq, deriv_Z2_eq] at hmode
  simp only [evanescentMode] at hmode
  simp only [mul_zero, Real.exp_zero, harg_t0 omega homega, Real.sin_pi_div_two, mul_one] at hmode
  have h1 := congrArg (fun v : ℝ => -v) hmode
  rw [neg_mul, neg_neg] at h1
  have h2 : (-(E0 / omega)) * omega ^ 2
      = (-(E0 / omega)) * (c0 ^ 2 * (cutoffWavenumber a ^ 2 - kappa ^ 2)) := by
    rw [h1]
    ring
  exact mul_left_cancel₀ hM h2

/-- The electric component `E_y`, without any frequency hypothesis. -/
private lemma E_comp_one (a E0 omega kappa t x y z : ℝ) :
    evanescentElectricField a E0 omega kappa t x y z 1
      = -(te10Profile a x * partialTime (evanescentMode E0 omega kappa) t z) := by
  simp [evanescentElectricField, separableElectricField]

/-- The magnetic component `B_x`, without any frequency hypothesis. -/
private lemma B_comp_zero (a E0 omega kappa t x y z : ℝ) :
    evanescentMagneticField a E0 omega kappa t x y z 0
      = -(te10Profile a x * partialZ (evanescentMode E0 omega kappa) t z) := by
  simp [evanescentMagneticField, separableMagneticField]

/-- The magnetic component `B_z`, without any frequency hypothesis. -/
private lemma B_comp_two (a E0 omega kappa t x y z : ℝ) :
    evanescentMagneticField a E0 omega kappa t x y z 2
      = deriv (te10Profile a) x * evanescentMode E0 omega kappa t z := by
  simp [evanescentMagneticField, separableMagneticField]

/-- The wavenumber times the half width is `π / 2`. -/
private lemma harg_half (a : ℝ) (ha : a ≠ 0) :
    (Real.pi / a) * (a / 2) = Real.pi / 2 := by
  have h1 : (Real.pi / a) * (a / 2) = (Real.pi * (a / a)) / 2 := by ring
  rw [h1, div_self ha, mul_one]

/-- The wavenumber times the full width is `π`. -/
private lemma harg_full (a : ℝ) (ha : a ≠ 0) :
    (Real.pi / a) * a = Real.pi :=
  div_mul_cancel₀ _ ha

/-- Strictly below cutoff the decay-rate radicand is positive. -/
private lemma decayRate_arg_pos (c : SpeedOfLight) (a omega : ℝ) (homega : 0 < omega)
    (hbelow : omega < (c : ℝ) * cutoffWavenumber a) :
    0 < cutoffWavenumber a ^ 2 - omega ^ 2 / (c : ℝ) ^ 2 := by
  have hc : 0 < (c : ℝ) := c.pos
  have hkc : 0 < cutoffWavenumber a :=
    pos_of_mul_pos_right (lt_trans homega hbelow) (le_of_lt hc)
  have hc2 : 0 < (c : ℝ) ^ 2 := pow_pos hc 2
  have hsq : omega ^ 2 < ((c : ℝ) * cutoffWavenumber a) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self (le_of_lt homega) hbelow
  have hlt : omega ^ 2 / (c : ℝ) ^ 2 < cutoffWavenumber a ^ 2 := by
    rw [div_lt_iff₀ hc2]
    calc omega ^ 2 < ((c : ℝ) * cutoffWavenumber a) ^ 2 := hsq
      _ = cutoffWavenumber a ^ 2 * (c : ℝ) ^ 2 := by ring
  linarith [hlt]

/-! ## C. The decay rate -/

/-- Strictly below cutoff the decay rate is positive. -/
lemma decayRate_pos (c : SpeedOfLight) (a omega : ℝ) (homega : 0 < omega)
    (hbelow : omega < (c : ℝ) * cutoffWavenumber a) :
    0 < decayRate c a omega := by
  unfold decayRate
  exact Real.sqrt_pos.mpr (decayRate_arg_pos c a omega homega hbelow)

/-- Strictly below cutoff the decay rate squares to `kc^2 - ω^2 / c0^2`. -/
lemma decayRate_sq (c : SpeedOfLight) (a omega : ℝ) (homega : 0 < omega)
    (hbelow : omega < (c : ℝ) * cutoffWavenumber a) :
    decayRate c a omega ^ 2 = cutoffWavenumber a ^ 2 - omega ^ 2 / (c : ℝ) ^ 2 := by
  unfold decayRate
  exact Real.sq_sqrt (le_of_lt (decayRate_arg_pos c a omega homega hbelow))

/-- Boundary case: at the cutoff `ω = c0 kc` the decay rate is zero. -/
lemma decayRate_at_cutoff (c : SpeedOfLight) (a : ℝ) :
    decayRate c a ((c : ℝ) * cutoffWavenumber a) = 0 := by
  have hc : (c : ℝ) ≠ 0 := ne_of_gt c.pos
  have hc2 : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hdiv : ((c : ℝ) * cutoffWavenumber a) ^ 2 / (c : ℝ) ^ 2
      = cutoffWavenumber a ^ 2 := by
    have hsq : ((c : ℝ) * cutoffWavenumber a) ^ 2
        = (c : ℝ) ^ 2 * cutoffWavenumber a ^ 2 := by ring
    rw [hsq]
    exact mul_div_cancel_left₀ _ hc2
  unfold decayRate
  rw [hdiv, sub_self, Real.sqrt_zero]

/-! ## D. Scalar equations and regularity -/

/-- The TE10 profile solves the profile equation with the cutoff wavenumber. -/
lemma te10Profile_profileEquation (a : ℝ) :
    profileEquation (te10Profile a) (cutoffWavenumber a) := by
  intro x
  rw [deriv_P1_fun]
  have h := (hasDerivAt_P2 a x).deriv
  rw [h]
  simp only [te10Profile]
  ring

/-- The TE10 profile is smooth. -/
lemma contDiff_te10Profile (a : ℝ) : ContDiff ℝ ∞ (te10Profile a) := by
  unfold te10Profile
  exact (contDiff_const.mul contDiff_id).sin

/-- The evanescent mode is jointly smooth in time and guide coordinate. -/
lemma contDiff_evanescentMode (E0 omega kappa : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (evanescentMode E0 omega kappa)) := by
  unfold Function.uncurry
  unfold evanescentMode
  exact (contDiff_const.mul (contDiff_const.mul contDiff_snd).exp).mul
    ((contDiff_const.mul contDiff_fst).sin)

/-- For a nonzero amplitude and frequency, the evanescent mode with rate `κ` solves the mode
equation exactly when `ω^2 = c0^2 (kc^2 - κ^2)`. -/
lemma evanescentMode_modeEquation_iff (c0 a E0 omega kappa : ℝ) (hE0 : E0 ≠ 0)
    (homega : omega ≠ 0) :
    modeEquation c0 (cutoffWavenumber a) (evanescentMode E0 omega kappa) ↔
      omega ^ 2 = c0 ^ 2 * (cutoffWavenumber a ^ 2 - kappa ^ 2) := by
  constructor
  · intro hmode
    exact rate_eq_of_point c0 a E0 omega kappa hE0 homega (hmode ((Real.pi / 2) / omega) 0)
  · intro hrate
    exact modeEquation_of_rate_eq c0 a E0 omega kappa hrate

/-- Strictly below cutoff, the evanescent mode with the decay rate solves the mode equation. -/
lemma evanescentMode_decayRate_modeEquation (c : SpeedOfLight) (a E0 omega : ℝ)
    (homega : 0 < omega) (hbelow : omega < (c : ℝ) * cutoffWavenumber a) :
    modeEquation c (cutoffWavenumber a) (evanescentMode E0 omega (decayRate c a omega)) := by
  apply modeEquation_of_rate_eq
  have hsq := decayRate_sq c a omega homega hbelow
  have hc : (c : ℝ) ≠ 0 := ne_of_gt c.pos
  have hc2 : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hmul := congrArg (fun v => v * (c : ℝ) ^ 2) hsq
  have hrhs : (cutoffWavenumber a ^ 2 - omega ^ 2 / (c : ℝ) ^ 2) * (c : ℝ) ^ 2
      = cutoffWavenumber a ^ 2 * (c : ℝ) ^ 2 - omega ^ 2 := by
    rw [sub_mul, div_mul_cancel₀ _ hc2]
  rw [hrhs] at hmul
  linarith [hmul]

/-! ## E. Field components -/

/-- The evanescent electric field is `(0, E0 sin (kc x) exp (-κ z) cos (ω t), 0)`. -/
lemma evanescentElectricField_apply (a E0 omega kappa : ℝ) (homega : omega ≠ 0)
    (t x y z : ℝ) :
    evanescentElectricField a E0 omega kappa t x y z =
      ![0, E0 * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z) *
        Real.cos (omega * t), 0] := by
  have hEv : evanescentElectricField a E0 omega kappa t x y z
      = ![0, -(te10Profile a x * partialTime (evanescentMode E0 omega kappa) t z), 0] := rfl
  have hcancel : E0 / omega * omega = E0 := div_mul_cancel₀ _ homega
  have hmid : -(te10Profile a x *
      (((-(E0 / omega)) * Real.exp (-kappa * z)) * (omega * Real.cos (omega * t))))
      = E0 * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z) * Real.cos (omega * t) := by
    have hfactor : -(te10Profile a x *
        (((-(E0 / omega)) * Real.exp (-kappa * z)) * (omega * Real.cos (omega * t))))
        = te10Profile a x * (E0 / omega * omega) * Real.exp (-kappa * z) *
          Real.cos (omega * t) := by
      ring
    rw [hfactor, hcancel]
    simp only [te10Profile]
    ring
  rw [hEv, partialTime_eq, hmid]

/-- The evanescent magnetic field is
`(-(κ E0 / ω) sin (kc x) exp (-κ z) sin (ω t), 0, -(kc E0 / ω) cos (kc x) exp (-κ z) sin (ω t))`.
-/
lemma evanescentMagneticField_apply (a E0 omega kappa : ℝ) (t x y z : ℝ) :
    evanescentMagneticField a E0 omega kappa t x y z =
      ![-(kappa * E0 / omega * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z) *
          Real.sin (omega * t)), 0,
        -(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x) *
          Real.exp (-kappa * z) * Real.sin (omega * t))] := by
  have hBv : evanescentMagneticField a E0 omega kappa t x y z
      = ![-(te10Profile a x * partialZ (evanescentMode E0 omega kappa) t z), 0,
        deriv (te10Profile a) x * evanescentMode E0 omega kappa t z] := rfl
  have hleft : -(te10Profile a x *
      (((-(E0 / omega)) * Real.sin (omega * t)) * (Real.exp (-kappa * z) * (-kappa))))
      = -(kappa * E0 / omega * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z)
        * Real.sin (omega * t)) := by
    simp only [te10Profile]
    ring
  have hright : (cutoffWavenumber a * Real.cos (cutoffWavenumber a * x)) *
      evanescentMode E0 omega kappa t z
      = -(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x)
        * Real.exp (-kappa * z) * Real.sin (omega * t)) := by
    simp only [evanescentMode]
    ring
  rw [hBv, partialZ_eq, deriv_P1, hleft, hright]

/-! ## F. Bulk equations -/

/-- **Bulk theorem for the evanescent mode.** Strictly below cutoff, the evanescent fields with
the decay rate satisfy the source-free vacuum Maxwell equations at every time and point. -/
theorem evanescent_sourceFreeVacuumMaxwell (c : SpeedOfLight) (a E0 omega : ℝ)
    (homega : 0 < omega) (hbelow : omega < (c : ℝ) * cutoffWavenumber a) :
    sourceFreeVacuumMaxwell c (evanescentElectricField a E0 omega (decayRate c a omega))
      (evanescentMagneticField a E0 omega (decayRate c a omega)) := by
  unfold evanescentElectricField
  unfold evanescentMagneticField
  exact separableFields_sourceFreeVacuumMaxwell _ _ _ _ (contDiff_te10Profile a)
    (contDiff_evanescentMode E0 omega (decayRate c a omega))
    (te10Profile_profileEquation a)
    (evanescentMode_decayRate_modeEquation c a E0 omega homega hbelow)

/-- Violated premise: for a guide of positive width, a nonzero amplitude and a nonzero frequency,
a rate `κ` with `ω^2 ≠ c0^2 (kc^2 - κ^2)` breaks the source-free vacuum Maxwell equations. -/
lemma not_evanescent_sourceFreeVacuumMaxwell_of_wrong_rate (c : SpeedOfLight)
    (a E0 omega kappa : ℝ) (ha : 0 < a) (hE0 : E0 ≠ 0) (homega : omega ≠ 0)
    (hrate : omega ^ 2 ≠ (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 - kappa ^ 2)) :
    ¬ sourceFreeVacuumMaxwell c (evanescentElectricField a E0 omega kappa)
      (evanescentMagneticField a E0 omega kappa) := by
  intro hmax
  have hax : te10Profile a (a / 2) ≠ 0 := by
    have haxv : te10Profile a (a / 2) = 1 := by
      simp only [te10Profile, cutoffWavenumber, harg_half a ha.ne', Real.sin_pi_div_two]
    rw [haxv]
    exact one_ne_zero
  have hmismatch : deriv (fun s => partialTime (evanescentMode E0 omega kappa) s 0)
        ((Real.pi / 2) / omega)
      ≠ (c : ℝ) ^ 2 * (deriv (fun w => partialZ (evanescentMode E0 omega kappa)
          ((Real.pi / 2) / omega) w) 0
        - cutoffWavenumber a ^ 2 * evanescentMode E0 omega kappa ((Real.pi / 2) / omega) 0) := by
    intro heq
    exact hrate (rate_eq_of_point (c : ℝ) a E0 omega kappa hE0 homega heq)
  exact not_sourceFree_of_modeEquation_failure (te10Profile a) (evanescentMode E0 omega kappa)
    (cutoffWavenumber a) c (contDiff_te10Profile a)
    (contDiff_evanescentMode E0 omega kappa) (te10Profile_profileEquation a)
    ((Real.pi / 2) / omega) (a / 2) 0 hax hmismatch hmax

/-! ## G. Side-wall traces -/

/-- **PEC traces.** For a guide of positive widths `a` and `b` and any rate, at every time the
evanescent fields satisfy the PEC traces on the four side walls. -/
theorem evanescent_rectangularGuidePECTraces (a b E0 omega kappa : ℝ) (ha : 0 < a) (hb : 0 < b)
    (t : ℝ) :
    rectangularGuidePECTraces a b (fieldAtTime (evanescentElectricField a E0 omega kappa) t)
      (fieldAtTime (evanescentMagneticField a E0 omega kappa) t) := by
  have ha' : a ≠ 0 := ha.ne'
  have harg3 : (Real.pi / a) * a = Real.pi := harg_full a ha'
  refine ⟨⟨ha, hb⟩, ?_, ?_, ?_, ?_⟩
  · intro y z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [fieldAtTime, E_comp_one, te10Profile, cutoffWavenumber, Real.sin_zero]
      · simp [fieldAtTime, evanescentElectricField, separableElectricField]
    · have hBv := evanescentMagneticField_apply a E0 omega kappa t 0 y z
      simp [fieldAtTime, normalMagneticOnXWall, hBv, cutoffWavenumber, Real.sin_zero]
  · intro y z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [fieldAtTime, E_comp_one, te10Profile, cutoffWavenumber, harg3, Real.sin_pi]
      · simp [fieldAtTime, evanescentElectricField, separableElectricField]
    · have hBv := evanescentMagneticField_apply a E0 omega kappa t a y z
      simp [fieldAtTime, normalMagneticOnXWall, hBv, cutoffWavenumber, harg3, Real.sin_pi]
  · intro x z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [fieldAtTime, evanescentElectricField, separableElectricField]
      · simp [fieldAtTime, evanescentElectricField, separableElectricField]
    · have hBv := evanescentMagneticField_apply a E0 omega kappa t x 0 z
      simp [fieldAtTime, normalMagneticOnYWall, hBv]
  · intro x z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [fieldAtTime, evanescentElectricField, separableElectricField]
      · simp [fieldAtTime, evanescentElectricField, separableElectricField]
    · have hBv := evanescentMagneticField_apply a E0 omega kappa t x b z
      simp [fieldAtTime, normalMagneticOnYWall, hBv]

/-! ## H. Nonvanishing -/

/-- Validation value: at `x = a / 2`, `t = z = 0` and any `y`, the electric component `E_y`
equals `E0`. -/
lemma evanescentElectricField_center (a E0 omega kappa : ℝ) (ha : a ≠ 0)
    (homega : omega ≠ 0) (y : ℝ) :
    evanescentElectricField a E0 omega kappa 0 (a / 2) y 0 1 = E0 := by
  have hEv := evanescentElectricField_apply a E0 omega kappa homega 0 (a / 2) y 0
  rw [hEv]
  simp [cutoffWavenumber, harg_half a ha, Real.sin_pi_div_two, Real.exp_zero, Real.cos_zero]

/-- For a nonzero amplitude the evanescent electric field is not identically zero. -/
lemma evanescentElectricField_ne_zero (a E0 omega kappa : ℝ) (ha : 0 < a) (hE0 : E0 ≠ 0)
    (homega : 0 < omega) :
    evanescentElectricField a E0 omega kappa ≠ 0 := by
  intro h
  have hcon : evanescentElectricField a E0 omega kappa 0 (a / 2) 0 0 1 = 0 :=
    congrArg (fun F : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ => F 0 (a / 2) 0 0 1) h
  rw [evanescentElectricField_center a E0 omega kappa ha.ne' homega.ne' 0] at hcon
  exact hE0 hcon

/-! ## I. Decay toward positive `z` -/

/-- The longitudinal dependence of both fields is the factor `exp (-κ z)` times their value at
`z = 0`. -/
lemma evanescentFields_eq_exp_smul (a E0 omega kappa : ℝ) (t x y z : ℝ) :
    evanescentElectricField a E0 omega kappa t x y z =
        Real.exp (-kappa * z) • evanescentElectricField a E0 omega kappa t x y 0 ∧
      evanescentMagneticField a E0 omega kappa t x y z =
        Real.exp (-kappa * z) • evanescentMagneticField a E0 omega kappa t x y 0 := by
  refine ⟨?_, ?_⟩
  · apply funext
    intro i
    obtain ⟨v, hv⟩ := i
    have h013 : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    obtain rfl | rfl | rfl := h013
    · rw [show (⟨0, hv⟩ : Fin 3) = 0 from rfl]
      have hEz0 : evanescentElectricField a E0 omega kappa t x y z 0 = 0 := by
        simp [evanescentElectricField, separableElectricField]
      have hE00 : evanescentElectricField a E0 omega kappa t x y 0 0 = 0 := by
        simp [evanescentElectricField, separableElectricField]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hEz0, hE00]
      exact (mul_zero _).symm
    · rw [show (⟨1, hv⟩ : Fin 3) = 1 from rfl]
      have hTz := partialTime_eq E0 omega kappa t z
      have hT0 := partialTime_eq E0 omega kappa t 0
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [E_comp_one, E_comp_one, hTz, hT0]
      simp only [mul_zero, Real.exp_zero]
      ring
    · rw [show (⟨2, hv⟩ : Fin 3) = 2 from rfl]
      have hEz2 : evanescentElectricField a E0 omega kappa t x y z 2 = 0 := by
        simp [evanescentElectricField, separableElectricField]
      have hE02 : evanescentElectricField a E0 omega kappa t x y 0 2 = 0 := by
        simp [evanescentElectricField, separableElectricField]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hEz2, hE02]
      exact (mul_zero _).symm
  · apply funext
    intro i
    obtain ⟨v, hv⟩ := i
    have h013 : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    obtain rfl | rfl | rfl := h013
    · rw [show (⟨0, hv⟩ : Fin 3) = 0 from rfl]
      have hZz := partialZ_eq E0 omega kappa t z
      have hZ0 := partialZ_eq E0 omega kappa t 0
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [B_comp_zero, B_comp_zero, hZz, hZ0]
      simp only [mul_zero, Real.exp_zero]
      ring
    · rw [show (⟨1, hv⟩ : Fin 3) = 1 from rfl]
      have hBz1 : evanescentMagneticField a E0 omega kappa t x y z 1 = 0 := by
        simp [evanescentMagneticField, separableMagneticField]
      have hB01 : evanescentMagneticField a E0 omega kappa t x y 0 1 = 0 := by
        simp [evanescentMagneticField, separableMagneticField]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hBz1, hB01]
      exact (mul_zero _).symm
    · rw [show (⟨2, hv⟩ : Fin 3) = 2 from rfl]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [B_comp_two, B_comp_two]
      simp only [evanescentMode]
      simp only [mul_zero, Real.exp_zero]
      ring

/-- **Exponential decay on the half-guide.** For a guide of positive width, `ω > 0` and a rate
`κ ≥ 0`, on `z ≥ 0` every electric component is bounded by `|E0| exp (-κ z)` and every magnetic
component by `((κ + kc) |E0| / ω) exp (-κ z)`. -/
theorem evanescentFields_abs_le (a E0 omega kappa : ℝ) (ha : 0 < a) (homega : 0 < omega)
    (hkappa : 0 ≤ kappa) (t x y z : ℝ) (hz : 0 ≤ z) (i : Fin 3) :
    |evanescentElectricField a E0 omega kappa t x y z i| ≤ |E0| * Real.exp (-kappa * z) ∧
      |evanescentMagneticField a E0 omega kappa t x y z i| ≤
        (kappa + cutoffWavenumber a) * |E0| / omega * Real.exp (-kappa * z) := by
  have _ := hz
  have homega' : omega ≠ 0 := homega.ne'
  have hkc : 0 ≤ cutoffWavenumber a :=
    div_nonneg (le_of_lt Real.pi_pos) (le_of_lt ha)
  have hEv := evanescentElectricField_apply a E0 omega kappa homega' t x y z
  have hBv := evanescentMagneticField_apply a E0 omega kappa t x y z
  have hexpnn : 0 ≤ Real.exp (-kappa * z) := le_of_lt (Real.exp_pos _)
  obtain ⟨v, hv⟩ := i
  have h013 : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  obtain rfl | rfl | rfl := h013
  · rw [show (⟨0, hv⟩ : Fin 3) = 0 from rfl]
    refine ⟨?_, ?_⟩
    · have hE0c : evanescentElectricField a E0 omega kappa t x y z 0 = 0 := by
        rw [hEv]; simp
      rw [hE0c, abs_zero]
      exact mul_nonneg (abs_nonneg _) hexpnn
    · have hB0c : evanescentMagneticField a E0 omega kappa t x y z 0
          = -(kappa * E0 / omega * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z)
            * Real.sin (omega * t)) := by
        rw [hBv]; simp
      have hST : |Real.sin (cutoffWavenumber a * x)| * |Real.sin (omega * t)| ≤ 1 := by
        have h1 : |Real.sin (cutoffWavenumber a * x)| * |Real.sin (omega * t)|
            ≤ 1 * |Real.sin (omega * t)| :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
        have h2 : (1 : ℝ) * |Real.sin (omega * t)| ≤ 1 := by
          have h2' : (1 : ℝ) * |Real.sin (omega * t)| ≤ 1 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) zero_le_one
          rwa [mul_one] at h2'
        linarith [h1, h2]
      have habs : |evanescentMagneticField a E0 omega kappa t x y z 0|
          = ((kappa * (|E0| / omega)) * Real.exp (-kappa * z))
            * (|Real.sin (cutoffWavenumber a * x)| * |Real.sin (omega * t)|) := by
        rw [hB0c]
        simp only [abs_neg, abs_mul, abs_div, abs_of_nonneg hkappa, abs_of_pos homega,
          abs_of_pos (Real.exp_pos _)]
        ring
      rw [habs]
      have hK : 0 ≤ kappa * (|E0| / omega) * Real.exp (-kappa * z) :=
        mul_nonneg (mul_nonneg hkappa (div_nonneg (abs_nonneg _) (le_of_lt homega))) hexpnn
      have hKK' : kappa * (|E0| / omega) * Real.exp (-kappa * z)
          ≤ (kappa + cutoffWavenumber a) * (|E0| / omega) * Real.exp (-kappa * z) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith [hkc])
            (div_nonneg (abs_nonneg _) (le_of_lt homega))) hexpnn
      calc ((kappa * (|E0| / omega)) * Real.exp (-kappa * z))
              * (|Real.sin (cutoffWavenumber a * x)| * |Real.sin (omega * t)|)
            ≤ (kappa * (|E0| / omega) * Real.exp (-kappa * z)) * 1 :=
              mul_le_mul_of_nonneg_left hST hK
          _ = kappa * (|E0| / omega) * Real.exp (-kappa * z) := mul_one _
          _ ≤ (kappa + cutoffWavenumber a) * (|E0| / omega) * Real.exp (-kappa * z) := hKK'
          _ = (kappa + cutoffWavenumber a) * |E0| / omega * Real.exp (-kappa * z) := by ring
  · rw [show (⟨1, hv⟩ : Fin 3) = 1 from rfl]
    refine ⟨?_, ?_⟩
    · have hE1c : evanescentElectricField a E0 omega kappa t x y z 1
          = E0 * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z) *
            Real.cos (omega * t) := by
        rw [hEv]; simp
      have hST : |Real.sin (cutoffWavenumber a * x)| * |Real.cos (omega * t)| ≤ 1 := by
        have h1 : |Real.sin (cutoffWavenumber a * x)| * |Real.cos (omega * t)|
            ≤ 1 * |Real.cos (omega * t)| :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
        have h2 : (1 : ℝ) * |Real.cos (omega * t)| ≤ 1 := by
          have h2' : (1 : ℝ) * |Real.cos (omega * t)| ≤ 1 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) zero_le_one
          rwa [mul_one] at h2'
        linarith [h1, h2]
      have habs : |evanescentElectricField a E0 omega kappa t x y z 1|
          = ((|E0| * Real.exp (-kappa * z))
            * (|Real.sin (cutoffWavenumber a * x)| * |Real.cos (omega * t)|)) := by
        rw [hE1c]
        simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
        ring
      rw [habs]
      have hAE : 0 ≤ |E0| * Real.exp (-kappa * z) := mul_nonneg (abs_nonneg _) hexpnn
      calc ((|E0| * Real.exp (-kappa * z))
              * (|Real.sin (cutoffWavenumber a * x)| * |Real.cos (omega * t)|))
            ≤ (|E0| * Real.exp (-kappa * z)) * 1 :=
              mul_le_mul_of_nonneg_left hST hAE
          _ = |E0| * Real.exp (-kappa * z) := mul_one _
    · have hB1c : evanescentMagneticField a E0 omega kappa t x y z 1 = 0 := by
        rw [hBv]; simp
      rw [hB1c, abs_zero]
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by linarith [hkappa, hkc]) (abs_nonneg _)) (le_of_lt homega))
        hexpnn
  · rw [show (⟨2, hv⟩ : Fin 3) = 2 from rfl]
    refine ⟨?_, ?_⟩
    · have hE2c : evanescentElectricField a E0 omega kappa t x y z 2 = 0 := by
        rw [hEv]; simp
      rw [hE2c, abs_zero]
      exact mul_nonneg (abs_nonneg _) hexpnn
    · have hB2c : evanescentMagneticField a E0 omega kappa t x y z 2
          = -(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x)
            * Real.exp (-kappa * z) * Real.sin (omega * t)) := by
        rw [hBv]; simp
      have hST : |Real.cos (cutoffWavenumber a * x)| * |Real.sin (omega * t)| ≤ 1 := by
        have h1 : |Real.cos (cutoffWavenumber a * x)| * |Real.sin (omega * t)|
            ≤ 1 * |Real.sin (omega * t)| :=
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
        have h2 : (1 : ℝ) * |Real.sin (omega * t)| ≤ 1 := by
          have h2' : (1 : ℝ) * |Real.sin (omega * t)| ≤ 1 * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) zero_le_one
          rwa [mul_one] at h2'
        linarith [h1, h2]
      have habs : |evanescentMagneticField a E0 omega kappa t x y z 2|
          = ((cutoffWavenumber a * (|E0| / omega)) * Real.exp (-kappa * z))
            * (|Real.cos (cutoffWavenumber a * x)| * |Real.sin (omega * t)|) := by
        rw [hB2c]
        simp only [abs_neg, abs_mul, abs_div, abs_of_pos homega, abs_of_nonneg hkc,
          abs_of_pos (Real.exp_pos _)]
        ring
      rw [habs]
      have hK : 0 ≤ cutoffWavenumber a * (|E0| / omega) * Real.exp (-kappa * z) :=
        mul_nonneg (mul_nonneg hkc (div_nonneg (abs_nonneg _) (le_of_lt homega))) hexpnn
      have hKK' : cutoffWavenumber a * (|E0| / omega) * Real.exp (-kappa * z)
          ≤ (kappa + cutoffWavenumber a) * (|E0| / omega) * Real.exp (-kappa * z) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith [hkappa])
            (div_nonneg (abs_nonneg _) (le_of_lt homega))) hexpnn
      calc ((cutoffWavenumber a * (|E0| / omega)) * Real.exp (-kappa * z))
              * (|Real.cos (cutoffWavenumber a * x)| * |Real.sin (omega * t)|)
            ≤ (cutoffWavenumber a * (|E0| / omega) * Real.exp (-kappa * z)) * 1 :=
              mul_le_mul_of_nonneg_left hST hK
          _ = cutoffWavenumber a * (|E0| / omega) * Real.exp (-kappa * z) := mul_one _
          _ ≤ (kappa + cutoffWavenumber a) * (|E0| / omega) * Real.exp (-kappa * z) := hKK'
          _ = (kappa + cutoffWavenumber a) * |E0| / omega * Real.exp (-kappa * z) := by ring

/-- For a positive rate every field component tends to zero as `z → ∞`. -/
lemma tendsto_evanescentFields_atTop (a E0 omega kappa : ℝ) (hkappa : 0 < kappa)
    (t x y : ℝ) (i : Fin 3) :
    Tendsto (fun z => evanescentElectricField a E0 omega kappa t x y z i) atTop (𝓝 0) ∧
      Tendsto (fun z => evanescentMagneticField a E0 omega kappa t x y z i) atTop (𝓝 0) := by
  have hκneg : -kappa < 0 := by linarith [hkappa]
  have hinner : Tendsto (fun z : ℝ => -kappa * z) atTop atBot := by
    simpa using (tendsto_const_mul_atBot_of_neg hκneg).mpr tendsto_id
  have hexp : Tendsto (fun z => Real.exp (-kappa * z)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hinner
  have hBv : ∀ z : ℝ, evanescentMagneticField a E0 omega kappa t x y z
      = ![-(kappa * E0 / omega * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z)
          * Real.sin (omega * t)), 0,
        -(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x)
          * Real.exp (-kappa * z) * Real.sin (omega * t))] :=
    fun z => evanescentMagneticField_apply a E0 omega kappa t x y z
  obtain ⟨v, hv⟩ := i
  have h013 : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  obtain rfl | rfl | rfl := h013
  · rw [show (⟨0, hv⟩ : Fin 3) = 0 from rfl]
    refine ⟨?_, ?_⟩
    · have hEz0 : ∀ z : ℝ, evanescentElectricField a E0 omega kappa t x y z 0 = 0 := by
        intro z
        simp [evanescentElectricField, separableElectricField]
      have hfun : (fun z => evanescentElectricField a E0 omega kappa t x y z 0)
          = fun _ => 0 := funext hEz0
      rw [hfun]
      exact tendsto_const_nhds
    · have hB0c : ∀ z : ℝ, evanescentMagneticField a E0 omega kappa t x y z 0
          = -(kappa * E0 / omega * Real.sin (cutoffWavenumber a * x) * Real.exp (-kappa * z)
            * Real.sin (omega * t)) := by
        intro z
        rw [hBv z]
        simp
      have hfun : (fun z => evanescentMagneticField a E0 omega kappa t x y z 0)
          = fun z => (-(kappa * E0 / omega * Real.sin (cutoffWavenumber a * x)
            * Real.sin (omega * t))) * Real.exp (-kappa * z) := by
        funext z
        rw [hB0c z]
        ring
      rw [hfun]
      simpa using hexp.const_mul
        (-(kappa * E0 / omega * Real.sin (cutoffWavenumber a * x) * Real.sin (omega * t)))
  · rw [show (⟨1, hv⟩ : Fin 3) = 1 from rfl]
    refine ⟨?_, ?_⟩
    · have hfun : (fun z => evanescentElectricField a E0 omega kappa t x y z 1)
          = fun z => (-(te10Profile a x * ((-(E0 / omega)) * (omega * Real.cos (omega * t)))))
            * Real.exp (-kappa * z) := by
        funext z
        rw [E_comp_one, partialTime_eq]
        ring
      rw [hfun]
      simpa using hexp.const_mul
        (-(te10Profile a x * ((-(E0 / omega)) * (omega * Real.cos (omega * t)))))
    · have hBz1 : ∀ z : ℝ, evanescentMagneticField a E0 omega kappa t x y z 1 = 0 := by
        intro z
        simp [evanescentMagneticField, separableMagneticField]
      have hfun : (fun z => evanescentMagneticField a E0 omega kappa t x y z 1)
          = fun _ => 0 := funext hBz1
      rw [hfun]
      exact tendsto_const_nhds
  · rw [show (⟨2, hv⟩ : Fin 3) = 2 from rfl]
    refine ⟨?_, ?_⟩
    · have hEz2 : ∀ z : ℝ, evanescentElectricField a E0 omega kappa t x y z 2 = 0 := by
        intro z
        simp [evanescentElectricField, separableElectricField]
      have hfun : (fun z => evanescentElectricField a E0 omega kappa t x y z 2)
          = fun _ => 0 := funext hEz2
      rw [hfun]
      exact tendsto_const_nhds
    · have hB2c : ∀ z : ℝ, evanescentMagneticField a E0 omega kappa t x y z 2
          = -(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x)
            * Real.exp (-kappa * z) * Real.sin (omega * t)) := by
        intro z
        rw [hBv z]
        simp
      have hfun : (fun z => evanescentMagneticField a E0 omega kappa t x y z 2)
          = fun z => (-(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x)
            * Real.sin (omega * t))) * Real.exp (-kappa * z) := by
        funext z
        rw [hB2c z]
        ring
      rw [hfun]
      simpa using hexp.const_mul
        (-(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x)
          * Real.sin (omega * t)))

/-- Decay is only toward positive `z`: for a guide of positive width, `E0 ≠ 0`, `ω > 0` and
`κ > 0`, the electric component `E_y` at `t = 0`, `x = a / 2` is unbounded on `z ≤ 0`. -/
lemma not_bddAbove_evanescentElectricField_nonpos (a E0 omega kappa : ℝ) (ha : 0 < a)
    (hE0 : E0 ≠ 0) (homega : 0 < omega) (hkappa : 0 < kappa) (y : ℝ) :
    ¬ ∃ C : ℝ, ∀ z : ℝ, z ≤ 0 →
      |evanescentElectricField a E0 omega kappa 0 (a / 2) y z 1| ≤ C := by
  intro hC
  obtain ⟨C, hC⟩ := hC
  have hE0abs : 0 < |E0| := abs_pos.mpr hE0
  have hκ : kappa ≠ 0 := hkappa.ne'
  have hval : ∀ z : ℝ, evanescentElectricField a E0 omega kappa 0 (a / 2) y z 1
      = E0 * Real.exp (-kappa * z) := by
    intro z
    have hEv := evanescentElectricField_apply a E0 omega kappa homega.ne' 0 (a / 2) y z
    have h1 : evanescentElectricField a E0 omega kappa 0 (a / 2) y z 1
        = E0 * Real.sin (cutoffWavenumber a * (a / 2)) * Real.exp (-kappa * z)
          * Real.cos (omega * 0) := by
      rw [hEv]
      simp
    rw [h1]
    simp only [cutoffWavenumber, harg_half a ha.ne', Real.sin_pi_div_two, mul_zero,
      Real.cos_zero, mul_one]
  have hYpos : 0 < (|C| + 1) / |E0| + 5 := by
    have hnn : 0 ≤ (|C| + 1) / |E0| :=
      div_nonneg (by linarith [abs_nonneg C]) (le_of_lt hE0abs)
    linarith [hnn]
  have hz0 : -(((|C| + 1) / |E0| + 5) / kappa) ≤ 0 := by
    have hnn : 0 ≤ ((|C| + 1) / |E0| + 5) / kappa :=
      div_nonneg (le_of_lt hYpos) (le_of_lt hkappa)
    linarith [hnn]
  have hκz0 : -kappa * (-(((|C| + 1) / |E0| + 5) / kappa)) = (|C| + 1) / |E0| + 5 := by
    have h1 : -kappa * (-(((|C| + 1) / |E0| + 5) / kappa))
        = kappa * (((|C| + 1) / |E0| + 5) / kappa) := by ring
    rw [h1, ← mul_div_assoc, mul_div_cancel_left₀ _ hκ]
  have hbig := hC _ hz0
  rw [hval] at hbig
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at hbig
  have hexp0 := Real.add_one_le_exp (-kappa * (-(((|C| + 1) / |E0| + 5) / kappa)))
  have hexp : ((|C| + 1) / |E0| + 5) + 1
      ≤ Real.exp (-kappa * (-(((|C| + 1) / |E0| + 5) / kappa))) := by
    have hY1 : ((|C| + 1) / |E0| + 5) + 1
        = (-kappa * (-(((|C| + 1) / |E0| + 5) / kappa))) + 1 := by rw [hκz0]
    rw [hY1]
    exact hexp0
  have heq : |E0| * ((((|C| + 1) / |E0| + 5) + 1)) = (|C| + 1) + 6 * |E0| := by
    have hcancel : |E0| * ((|C| + 1) / |E0|) = |C| + 1 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hE0abs.ne']
    calc |E0| * (((|C| + 1) / |E0| + 5) + 1)
        = |E0| * ((|C| + 1) / |E0|) + |E0| * 6 := by ring
      _ = (|C| + 1) + 6 * |E0| := by rw [hcancel]; ring
  have hmul : (|C| + 1) + 6 * |E0|
      ≤ |E0| * Real.exp (-kappa * (-(((|C| + 1) / |E0| + 5) / kappa))) := by
    have h1 : (|C| + 1) + 6 * |E0| = |E0| * ((((|C| + 1) / |E0| + 5) + 1)) := heq.symm
    rw [h1]
    exact mul_le_mul_of_nonneg_left hexp (le_of_lt hE0abs)
  linarith [hbig, hmul, le_abs_self C, hE0abs]

/-! ## J. Main result -/

/-- **Evanescent TE10 field below cutoff.** For guide widths `a, b > 0`, `E0 ≠ 0` and
`0 < ω < c0 kc`, the decay rate `κ = sqrt (kc^2 - ω^2 / c0^2)` is positive with
`κ^2 = kc^2 - ω^2 / c0^2`; the evanescent fields satisfy the source-free vacuum Maxwell
equations and the PEC traces on all four side walls at every time; the electric field is not
identically zero; and on the half-guide `z ≥ 0` every component decays like `exp (-κ z)`. -/
theorem te10Evanescent_correct (c : SpeedOfLight) (a b E0 omega : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hE0 : E0 ≠ 0) (homega : 0 < omega)
    (hbelow : omega < (c : ℝ) * cutoffWavenumber a) :
    0 < decayRate c a omega ∧
      decayRate c a omega ^ 2 = cutoffWavenumber a ^ 2 - omega ^ 2 / (c : ℝ) ^ 2 ∧
      sourceFreeVacuumMaxwell c (evanescentElectricField a E0 omega (decayRate c a omega))
        (evanescentMagneticField a E0 omega (decayRate c a omega)) ∧
      (∀ t : ℝ, rectangularGuidePECTraces a b
        (fieldAtTime (evanescentElectricField a E0 omega (decayRate c a omega)) t)
        (fieldAtTime (evanescentMagneticField a E0 omega (decayRate c a omega)) t)) ∧
      evanescentElectricField a E0 omega (decayRate c a omega) ≠ 0 ∧
      (∀ t x y z : ℝ, 0 ≤ z → ∀ i : Fin 3,
        |evanescentElectricField a E0 omega (decayRate c a omega) t x y z i| ≤
            |E0| * Real.exp (-decayRate c a omega * z) ∧
          |evanescentMagneticField a E0 omega (decayRate c a omega) t x y z i| ≤
            (decayRate c a omega + cutoffWavenumber a) * |E0| / omega *
              Real.exp (-decayRate c a omega * z)) := by
  have hκpos : 0 < decayRate c a omega := decayRate_pos c a omega homega hbelow
  refine ⟨hκpos, decayRate_sq c a omega homega hbelow,
    evanescent_sourceFreeVacuumMaxwell c a E0 omega homega hbelow, ?_, ?_, ?_⟩
  · intro t
    exact evanescent_rectangularGuidePECTraces a b E0 omega (decayRate c a omega) ha hb t
  · exact evanescentElectricField_ne_zero a E0 omega (decayRate c a omega) ha hE0 homega
  · intro t x y z hz i
    exact evanescentFields_abs_le a E0 omega (decayRate c a omega) ha homega (le_of_lt hκpos)
      t x y z hz i

end PhyslibExt.Electromagnetism.VacuumTE10Evanescent
