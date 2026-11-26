/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.RectangularPECTraces
public import PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Vacuum TE10 mode of a rectangular guide

The TE10 mode of a hollow rectangular guide as a separable vacuum Maxwell field, its side-wall
traces, its dispersion relation and its cutoff.

## i. Overview

Let `a > 0` be the guide width along `x`, `kc = π / a` the TE10 cutoff wavenumber, `c` the
speed of light, `E0` an amplitude and `ω`, `β` a frequency and a propagation constant. The TE10
mode is the separable field with transverse profile `sin (kc x)` and longitudinal mode
`f(t, z) = -(E0 / ω) sin (ω t - β z)`, whose components are
`E = (0, E0 sin (kc x) cos (ω t - β z), 0)` and
`B = (-(β E0 / ω) sin (kc x) cos (ω t - β z), 0, -(kc E0 / ω) cos (kc x) sin (ω t - β z))`.

Under the dispersion relation `ω^2 = c^2 (kc^2 + β^2)` these fields satisfy the source-free
vacuum Maxwell equations at every time and point, through the general theorem for separable
fields; for a nonzero amplitude and frequency the dispersion relation is also necessary. For a
height `b > 0`, at every time the fields satisfy the perfect-conductor traces on the four side
walls `x = 0, a`, `y = 0, b` (there are no end caps), and for `E0 ≠ 0` the electric field is
not identically zero, with `E_y = E0` at `x = a / 2`, `t = z = 0`.

For `ω > 0` a nonnegative propagation constant exists exactly when `ω ≥ c kc`; it is then
unique and equal to `sqrt (ω^2 / c^2 - kc^2)`, and it vanishes exactly at the cutoff
`ω = c kc`. Below cutoff the dispersion relation has no real solution of either sign. The
width hypothesis `0 < a` matters: Lean's `π / 0 = 0` makes `a = 0` a degenerate guide whose
fields vanish identically.

## ii. Key results

- `te10_sourceFreeVacuumMaxwell`: the TE10 fields satisfy the source-free vacuum Maxwell
  equations under the dispersion relation.
- `not_te10_sourceFreeVacuumMaxwell_of_not_dispersion`: a dispersion mismatch breaks them.
- `te10_rectangularGuidePECTraces`: the PEC traces on the four side walls at every time.
- `te10ElectricField_center` and `te10ElectricField_ne_zero`: the field is nonzero.
- `exists_nonneg_te10Dispersion_iff`: a propagating mode exists exactly at or above cutoff.
- `nonneg_te10Dispersion_iff_eq_propagationConstant`: its propagation constant is unique.
- `te10Dispersion_at_cutoff_iff` and `not_exists_te10Dispersion_below_cutoff`: the cutoff
  equality and the absence of a real propagation constant below cutoff.
- `te10Mode_correct`: the combined statement.

## iii. Table of contents

- A. The TE10 mode
- B. Auxiliary computations
- C. Scalar equations and regularity
- D. Field components
- E. Bulk equations
- F. Side-wall traces
- G. Nonvanishing
- H. Cutoff
- I. Main result

## iv. References

- D. M. Pozar, *Microwave Engineering*, fourth edition, Wiley, 2012, Section 3.3: the TE10
  mode of a rectangular waveguide, its cutoff frequency and its propagation constant.
- J. D. Jackson, *Classical Electrodynamics*, third edition, Wiley, 1998, Sections 8.3 and 8.4:
  boundary conditions at a perfect conductor and modes of a rectangular waveguide.

-/

@[expose] public section

open scoped ContDiff

namespace PhyslibExt.Electromagnetism.VacuumTE10Mode

open PhyslibExt.Electromagnetism.RectangularPECTraces
open PhyslibExt.Electromagnetism.SeparableVacuumMaxwell

/-! ## A. The TE10 mode -/

/-- The TE10 cutoff wavenumber `kc = π / a` of a guide of width `a`. -/
noncomputable def cutoffWavenumber (a : ℝ) : ℝ := Real.pi / a

/-- The TE10 transverse profile `sin (kc x)`. -/
noncomputable def te10Profile (a : ℝ) : ℝ → ℝ :=
  fun x => Real.sin (cutoffWavenumber a * x)

/-- The propagating longitudinal mode `f(t, z) = -(E0 / ω) sin (ω t - β z)`. -/
noncomputable def te10Mode (E0 omega beta : ℝ) : ℝ → ℝ → ℝ :=
  fun t z => -(E0 / omega) * Real.sin (omega * t - beta * z)

/-- The TE10 electric field, the separable electric field of the TE10 profile and mode. -/
noncomputable def te10ElectricField (a E0 omega beta : ℝ) : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  separableElectricField (te10Profile a) (te10Mode E0 omega beta)

/-- The TE10 magnetic field, the separable magnetic field of the TE10 profile and mode. -/
noncomputable def te10MagneticField (a E0 omega beta : ℝ) : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  separableMagneticField (te10Profile a) (te10Mode E0 omega beta)

/-- A field of time and three coordinates frozen at time `t`, as the point-to-vector map on
which the PEC trace predicates are stated. -/
def fieldAtTime (F : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ) (t : ℝ) : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  fun p => F t (p 0) (p 1) (p 2)

/-- The TE10 dispersion relation `ω^2 = c0^2 (kc^2 + β^2)`. -/
def te10Dispersion (c0 a omega beta : ℝ) : Prop :=
  omega ^ 2 = c0 ^ 2 * (cutoffWavenumber a ^ 2 + beta ^ 2)

/-- The propagation constant `sqrt (ω^2 / c0^2 - kc^2)`; meaningful at or above cutoff. -/
noncomputable def propagationConstant (c0 a omega : ℝ) : ℝ :=
  Real.sqrt (omega ^ 2 / c0 ^ 2 - cutoffWavenumber a ^ 2)

/-! ## B. Auxiliary computations -/

/-- Derivative of the profile argument `kc x`. -/
private lemma hasDerivAt_profileInner (a x : ℝ) :
    HasDerivAt (fun s : ℝ => cutoffWavenumber a * s) (cutoffWavenumber a) x := by
  have h := (hasDerivAt_id x).const_mul (cutoffWavenumber a)
  simpa using h

/-- Time derivative of the phase `ω t - β z`. -/
private lemma hasDerivAt_modeInner_t (omega beta z t : ℝ) :
    HasDerivAt (fun s : ℝ => omega * s - beta * z) omega t := by
  have h := ((hasDerivAt_id t).const_mul omega).sub_const (beta * z)
  simpa using h

/-- Guide-coordinate derivative of the phase `ω t - β z`. -/
private lemma hasDerivAt_modeInner_z (omega beta t z : ℝ) :
    HasDerivAt (fun w : ℝ => omega * t - beta * w) (-beta) z := by
  have hraw : HasDerivAt (fun w : ℝ => (-beta) * w + omega * t) (-beta) z := by
    have h := ((hasDerivAt_id z).const_mul (-beta)).add_const (omega * t)
    simpa using h
  refine hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  change omega * t - beta * w = (-beta) * w + omega * t
  ring

/-- First derivative of the TE10 profile. -/
private lemma deriv_te10Profile_eq (a x : ℝ) :
    deriv (te10Profile a) x = cutoffWavenumber a * Real.cos (cutoffWavenumber a * x) := by
  have h1 := hasDerivAt_profileInner a x
  have h2 : HasDerivAt (fun s : ℝ => Real.sin (cutoffWavenumber a * s))
      (Real.cos (cutoffWavenumber a * x) * cutoffWavenumber a) x := h1.sin
  have h3 := h2.deriv
  change deriv (fun s : ℝ => Real.sin (cutoffWavenumber a * s)) x = _
  rw [h3]
  ring

/-- Time derivative of the TE10 mode. -/
private lemma partialTime_te10Mode_eq (E0 omega beta t z : ℝ) :
    partialTime (te10Mode E0 omega beta) t z
      = -(E0 / omega) * (Real.cos (omega * t - beta * z) * omega) := by
  have h1 := hasDerivAt_modeInner_t omega beta z t
  have h2 : HasDerivAt (fun s : ℝ => Real.sin (omega * s - beta * z))
      (Real.cos (omega * t - beta * z) * omega) t := h1.sin
  have h3 : HasDerivAt (fun s : ℝ => -(E0 / omega) * Real.sin (omega * s - beta * z))
      (-(E0 / omega) * (Real.cos (omega * t - beta * z) * omega)) t :=
    h2.const_mul (-(E0 / omega))
  have h4 := h3.deriv
  change deriv (fun s : ℝ => te10Mode E0 omega beta s z) t = _
  change deriv (fun s : ℝ => -(E0 / omega) * Real.sin (omega * s - beta * z)) t = _
  exact h4

/-- Guide-coordinate derivative of the TE10 mode. -/
private lemma partialZ_te10Mode_eq (E0 omega beta t z : ℝ) :
    partialZ (te10Mode E0 omega beta) t z
      = -(E0 / omega) * (Real.cos (omega * t - beta * z) * -beta) := by
  have h1 := hasDerivAt_modeInner_z omega beta t z
  have h2 : HasDerivAt (fun w : ℝ => Real.sin (omega * t - beta * w))
      (Real.cos (omega * t - beta * z) * -beta) z := h1.sin
  have h3 : HasDerivAt (fun w : ℝ => -(E0 / omega) * Real.sin (omega * t - beta * w))
      (-(E0 / omega) * (Real.cos (omega * t - beta * z) * -beta)) z :=
    h2.const_mul (-(E0 / omega))
  have h4 := h3.deriv
  change deriv ((te10Mode E0 omega beta) t) z = _
  change deriv (fun w : ℝ => -(E0 / omega) * Real.sin (omega * t - beta * w)) z = _
  exact h4

/-- Second time derivative of the TE10 mode. -/
private lemma deriv_partialTime_te10Mode_eq (E0 omega beta t z : ℝ) :
    deriv (fun s => partialTime (te10Mode E0 omega beta) s z) t
      = -(omega ^ 2) * te10Mode E0 omega beta t z := by
  have hfun : (fun s => partialTime (te10Mode E0 omega beta) s z)
      = fun s => -(E0 / omega) * (Real.cos (omega * s - beta * z) * omega) :=
    funext (fun s => partialTime_te10Mode_eq E0 omega beta s z)
  rw [hfun]
  have h1 := hasDerivAt_modeInner_t omega beta z t
  have h2 : HasDerivAt (fun s : ℝ => Real.cos (omega * s - beta * z))
      (-Real.sin (omega * t - beta * z) * omega) t := h1.cos
  have h3 : HasDerivAt (fun s : ℝ => Real.cos (omega * s - beta * z) * omega)
      ((-Real.sin (omega * t - beta * z) * omega) * omega) t := h2.mul_const omega
  have h4 : HasDerivAt
      (fun s : ℝ => -(E0 / omega) * (Real.cos (omega * s - beta * z) * omega))
      (-(E0 / omega) * (((-Real.sin (omega * t - beta * z)) * omega) * omega)) t :=
    h3.const_mul (-(E0 / omega))
  have h5 := h4.deriv
  rw [h5]
  change -(E0 / omega) * (((-Real.sin (omega * t - beta * z)) * omega) * omega)
    = -(omega ^ 2) * te10Mode E0 omega beta t z
  change -(E0 / omega) * (((-Real.sin (omega * t - beta * z)) * omega) * omega)
    = -(omega ^ 2) * (-(E0 / omega) * Real.sin (omega * t - beta * z))
  ring

/-- Second guide-coordinate derivative of the TE10 mode. -/
private lemma deriv_partialZ_te10Mode_eq (E0 omega beta t z : ℝ) :
    deriv (fun w => partialZ (te10Mode E0 omega beta) t w) z
      = -(beta ^ 2) * te10Mode E0 omega beta t z := by
  have hfun : (fun w => partialZ (te10Mode E0 omega beta) t w)
      = fun w => -(E0 / omega) * (Real.cos (omega * t - beta * w) * -beta) :=
    funext (fun w => partialZ_te10Mode_eq E0 omega beta t w)
  rw [hfun]
  have h1 := hasDerivAt_modeInner_z omega beta t z
  have h2 : HasDerivAt (fun w : ℝ => Real.cos (omega * t - beta * w))
      (-Real.sin (omega * t - beta * z) * -beta) z := h1.cos
  have h3 : HasDerivAt (fun w : ℝ => Real.cos (omega * t - beta * w) * -beta)
      ((-Real.sin (omega * t - beta * z) * -beta) * -beta) z := h2.mul_const (-beta)
  have h4 : HasDerivAt
      (fun w : ℝ => -(E0 / omega) * (Real.cos (omega * t - beta * w) * -beta))
      (-(E0 / omega) * (((-Real.sin (omega * t - beta * z)) * -beta) * -beta)) z :=
    h3.const_mul (-(E0 / omega))
  have h5 := h4.deriv
  rw [h5]
  change -(E0 / omega) * (((-Real.sin (omega * t - beta * z)) * -beta) * -beta)
    = -(beta ^ 2) * te10Mode E0 omega beta t z
  change -(E0 / omega) * (((-Real.sin (omega * t - beta * z)) * -beta) * -beta)
    = -(beta ^ 2) * (-(E0 / omega) * Real.sin (omega * t - beta * z))
  ring

/-- The TE10 mode is nonzero at the quarter period `t = π / (2 ω)`, `z = 0`. -/
private lemma te10Mode_ne_zero_at (E0 omega beta : ℝ) (hE0 : E0 ≠ 0)
    (homega : omega ≠ 0) :
    te10Mode E0 omega beta ((Real.pi / 2) / omega) 0 ≠ 0 := by
  change -(E0 / omega) * Real.sin (omega * ((Real.pi / 2) / omega) - beta * 0) ≠ 0
  have harg : omega * ((Real.pi / 2) / omega) - beta * 0 = Real.pi / 2 := by
    rw [mul_zero, sub_zero, mul_div_cancel₀ _ homega]
  rw [harg, Real.sin_pi_div_two, mul_one]
  exact neg_ne_zero.mpr (div_ne_zero hE0 homega)

/-- The mode equation at one point where the mode is nonzero forces the dispersion relation. -/
private lemma dispersion_of_algebraic (c0 kc omega beta f0 : ℝ) (hf0 : f0 ≠ 0)
    (h : -(omega ^ 2) * f0 = c0 ^ 2 * (-(beta ^ 2) * f0 - kc ^ 2 * f0)) :
    omega ^ 2 = c0 ^ 2 * (kc ^ 2 + beta ^ 2) := by
  have hfactor : f0 * (-(omega ^ 2) + c0 ^ 2 * beta ^ 2 + c0 ^ 2 * kc ^ 2) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hfactor with h0 | h0
  · exact absurd h0 hf0
  · linear_combination -h0

/-- The dispersion relation gives the mode equation. -/
private lemma te10Mode_modeEquation_of_dispersion (c0 a E0 omega beta : ℝ)
    (hdisp : te10Dispersion c0 a omega beta) :
    modeEquation c0 (cutoffWavenumber a) (te10Mode E0 omega beta) := by
  intro t z
  rw [deriv_partialTime_te10Mode_eq, deriv_partialZ_te10Mode_eq]
  have hdisp' : omega ^ 2 = c0 ^ 2 * (cutoffWavenumber a ^ 2 + beta ^ 2) := hdisp
  linear_combination (-(te10Mode E0 omega beta t z)) * hdisp'

/-- The cutoff wavenumber of a guide of positive width is positive. -/
private lemma cutoffWavenumber_pos (a : ℝ) (ha : 0 < a) :
    0 < cutoffWavenumber a := by
  unfold cutoffWavenumber
  exact div_pos Real.pi_pos ha

/-- `kc a = π`. -/
private lemma cutoffWavenumber_mul_self (a : ℝ) (ha : a ≠ 0) :
    cutoffWavenumber a * a = Real.pi := by
  unfold cutoffWavenumber
  exact div_mul_cancel₀ _ ha

/-- `kc (a / 2) = π / 2`. -/
private lemma cutoffWavenumber_mul_half (a : ℝ) (ha : a ≠ 0) :
    cutoffWavenumber a * (a / 2) = Real.pi / 2 := by
  unfold cutoffWavenumber
  rw [show Real.pi / a * (a / 2) = (Real.pi / a * a) / 2 from by ring,
    div_mul_cancel₀ _ ha]

/-- At or above cutoff the argument of the square root is nonnegative. -/
private lemma propagationConstant_arg_nonneg (c : SpeedOfLight) (a omega : ℝ)
    (ha : 0 < a) (hcut : (c : ℝ) * cutoffWavenumber a ≤ omega) :
    0 ≤ omega ^ 2 / (c : ℝ) ^ 2 - cutoffWavenumber a ^ 2 := by
  have hc0 : 0 < (c : ℝ) := c.pos
  have hkc : 0 < cutoffWavenumber a := cutoffWavenumber_pos a ha
  have hc02 : 0 < (c : ℝ) ^ 2 := pow_pos hc0 2
  have hsq : ((c : ℝ) * cutoffWavenumber a) ^ 2 ≤ omega ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hc0.le hkc.le) hcut 2
  have h2 : (c : ℝ) ^ 2 * cutoffWavenumber a ^ 2 ≤ omega ^ 2 := by
    rwa [mul_pow] at hsq
  rw [sub_nonneg, le_div_iff₀ hc02]
  linear_combination h2

/-- At or above cutoff the propagation constant solves the dispersion relation. -/
private lemma te10Dispersion_propagationConstant (c : SpeedOfLight) (a omega : ℝ)
    (ha : 0 < a) (hcut : (c : ℝ) * cutoffWavenumber a ≤ omega) :
    te10Dispersion c a omega (propagationConstant c a omega) := by
  have hX := propagationConstant_arg_nonneg c a omega ha hcut
  have hc0ne : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c.pos)
  change omega ^ 2 = (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 + propagationConstant c a omega ^ 2)
  change omega ^ 2 = (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 +
    Real.sqrt (omega ^ 2 / (c : ℝ) ^ 2 - cutoffWavenumber a ^ 2) ^ 2)
  rw [Real.sq_sqrt hX, add_sub_cancel]
  exact (mul_div_cancel₀ _ hc0ne).symm

/-- The dispersion relation forces `(c kc)^2 ≤ ω^2`. -/
private lemma sq_le_of_dispersion (c : SpeedOfLight) (a omega beta : ℝ)
    (hdisp : te10Dispersion c a omega beta) :
    ((c : ℝ) * cutoffWavenumber a) ^ 2 ≤ omega ^ 2 := by
  have hdisp' : omega ^ 2 = (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 + beta ^ 2) := hdisp
  rw [mul_pow, hdisp']
  have h := mul_nonneg (sq_nonneg (c : ℝ)) (sq_nonneg beta)
  linarith

/-! ## C. Scalar equations and regularity -/

/-- The TE10 profile solves the profile equation with the cutoff wavenumber. -/
lemma te10Profile_profileEquation (a : ℝ) :
    profileEquation (te10Profile a) (cutoffWavenumber a) := by
  have hder : deriv (te10Profile a)
      = fun x => cutoffWavenumber a * Real.cos (cutoffWavenumber a * x) :=
    funext (deriv_te10Profile_eq a)
  intro x
  rw [hder]
  have h1 := hasDerivAt_profileInner a x
  have h2 : HasDerivAt (fun s : ℝ => Real.cos (cutoffWavenumber a * s))
      (-Real.sin (cutoffWavenumber a * x) * cutoffWavenumber a) x := h1.cos
  have h3 : HasDerivAt (fun s : ℝ => cutoffWavenumber a * Real.cos (cutoffWavenumber a * s))
      (cutoffWavenumber a * (-Real.sin (cutoffWavenumber a * x) * cutoffWavenumber a)) x :=
    h2.const_mul (cutoffWavenumber a)
  have h4 := h3.deriv
  rw [h4]
  change cutoffWavenumber a * (-Real.sin (cutoffWavenumber a * x) * cutoffWavenumber a)
    = -(cutoffWavenumber a ^ 2) * Real.sin (cutoffWavenumber a * x)
  ring

/-- The TE10 profile is smooth. -/
lemma contDiff_te10Profile (a : ℝ) : ContDiff ℝ ∞ (te10Profile a) := by
  have hinner : ContDiff ℝ ∞ (fun x : ℝ => cutoffWavenumber a * x) :=
    contDiff_const.mul contDiff_id
  exact Real.contDiff_sin.comp hinner

/-- The TE10 mode is jointly smooth in time and guide coordinate. -/
lemma contDiff_te10Mode (E0 omega beta : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (te10Mode E0 omega beta)) := by
  have hfst : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1) := contDiff_id.fst
  have hsnd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2) := contDiff_id.snd
  have hωt : ContDiff ℝ ∞ (fun p : ℝ × ℝ => omega * p.1) := contDiff_const.mul hfst
  have hβz : ContDiff ℝ ∞ (fun p : ℝ × ℝ => beta * p.2) := contDiff_const.mul hsnd
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => omega * p.1 - beta * p.2) := hωt.sub hβz
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.sin (omega * p.1 - beta * p.2)) :=
    Real.contDiff_sin.comp h1
  have h3 : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => -(E0 / omega) * Real.sin (omega * p.1 - beta * p.2)) :=
    contDiff_const.mul h2
  exact h3

/-- For a nonzero amplitude and frequency, the TE10 mode solves the mode equation exactly under
the dispersion relation. -/
lemma te10Mode_modeEquation_iff (c0 a E0 omega beta : ℝ) (hE0 : E0 ≠ 0)
    (homega : omega ≠ 0) :
    modeEquation c0 (cutoffWavenumber a) (te10Mode E0 omega beta) ↔
      te10Dispersion c0 a omega beta := by
  constructor
  · intro hmode
    have hpt := hmode ((Real.pi / 2) / omega) 0
    rw [deriv_partialTime_te10Mode_eq, deriv_partialZ_te10Mode_eq] at hpt
    exact dispersion_of_algebraic _ _ _ _ _
      (te10Mode_ne_zero_at E0 omega beta hE0 homega) hpt
  · intro hdisp
    exact te10Mode_modeEquation_of_dispersion c0 a E0 omega beta hdisp

/-! ## D. Field components -/

/-- The TE10 electric field is `(0, E0 sin (kc x) cos (ω t - β z), 0)`. -/
lemma te10ElectricField_apply (a E0 omega beta : ℝ) (homega : omega ≠ 0)
    (t x y z : ℝ) :
    te10ElectricField a E0 omega beta t x y z =
      ![0, E0 * Real.sin (cutoffWavenumber a * x) * Real.cos (omega * t - beta * z), 0] := by
  have hpt := partialTime_te10Mode_eq E0 omega beta t z
  change ![0, -((te10Profile a) x * partialTime (te10Mode E0 omega beta) t z), 0] = _
  rw [hpt]
  have hmid : -((te10Profile a) x * (-(E0 / omega) * (Real.cos (omega * t - beta * z) * omega)))
      = E0 * Real.sin (cutoffWavenumber a * x) * Real.cos (omega * t - beta * z) := by
    change -((Real.sin (cutoffWavenumber a * x)) *
      (-(E0 / omega) * (Real.cos (omega * t - beta * z) * omega))) = _
    field_simp
  rw [hmid]

/-- The TE10 magnetic field is
`(-(β E0 / ω) sin (kc x) cos (ω t - β z), 0, -(kc E0 / ω) cos (kc x) sin (ω t - β z))`. -/
lemma te10MagneticField_apply (a E0 omega beta : ℝ) (t x y z : ℝ) :
    te10MagneticField a E0 omega beta t x y z =
      ![-(beta * E0 / omega * Real.sin (cutoffWavenumber a * x) *
          Real.cos (omega * t - beta * z)), 0,
        -(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x) *
          Real.sin (omega * t - beta * z))] := by
  have hPZ := partialZ_te10Mode_eq E0 omega beta t z
  have hPA := deriv_te10Profile_eq a x
  change ![-(te10Profile a x * partialZ (te10Mode E0 omega beta) t z), 0,
      deriv (te10Profile a) x * te10Mode E0 omega beta t z] = _
  rw [hPZ, hPA]
  have e1 : -((te10Profile a) x * (-(E0 / omega) * (Real.cos (omega * t - beta * z) * -beta)))
      = -(beta * E0 / omega * Real.sin (cutoffWavenumber a * x) *
        Real.cos (omega * t - beta * z)) := by
    unfold te10Profile
    ring
  have e3 : (cutoffWavenumber a * Real.cos (cutoffWavenumber a * x)) *
      te10Mode E0 omega beta t z
      = -(cutoffWavenumber a * E0 / omega * Real.cos (cutoffWavenumber a * x) *
        Real.sin (omega * t - beta * z)) := by
    unfold te10Mode
    ring
  rw [e1, e3]

/-! ## E. Bulk equations -/

/-- **Bulk theorem for the TE10 mode.** Under the dispersion relation at the speed `c`, the TE10
fields satisfy the source-free vacuum Maxwell equations at every time and point, in particular in
the guide interior. -/
theorem te10_sourceFreeVacuumMaxwell (c : SpeedOfLight) (a E0 omega beta : ℝ)
    (hdisp : te10Dispersion c a omega beta) :
    sourceFreeVacuumMaxwell c (te10ElectricField a E0 omega beta)
      (te10MagneticField a E0 omega beta) := by
  exact separableFields_sourceFreeVacuumMaxwell (te10Profile a) (te10Mode E0 omega beta)
    (cutoffWavenumber a) c (contDiff_te10Profile a) (contDiff_te10Mode E0 omega beta)
    (te10Profile_profileEquation a)
    (te10Mode_modeEquation_of_dispersion (c : ℝ) a E0 omega beta hdisp)

/-- Violated premise: for a guide of positive width, a nonzero amplitude and a nonzero frequency,
a dispersion mismatch breaks the source-free vacuum Maxwell equations. -/
lemma not_te10_sourceFreeVacuumMaxwell_of_not_dispersion (c : SpeedOfLight)
    (a E0 omega beta : ℝ) (ha : 0 < a) (hE0 : E0 ≠ 0) (homega : omega ≠ 0)
    (hdisp : ¬ te10Dispersion c a omega beta) :
    ¬ sourceFreeVacuumMaxwell c (te10ElectricField a E0 omega beta)
      (te10MagneticField a E0 omega beta) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hkc2 := cutoffWavenumber_mul_half a ha0
  have hax : te10Profile a (a / 2) ≠ 0 := by
    change Real.sin (cutoffWavenumber a * (a / 2)) ≠ 0
    rw [hkc2, Real.sin_pi_div_two]
    exact one_ne_zero
  have hf0 := te10Mode_ne_zero_at E0 omega beta hE0 homega
  have hmismatch : deriv (fun s => partialTime (te10Mode E0 omega beta) s 0)
      ((Real.pi / 2) / omega)
      ≠ (c : ℝ) ^ 2 * (deriv (fun w => partialZ (te10Mode E0 omega beta)
        ((Real.pi / 2) / omega) w) 0
        - cutoffWavenumber a ^ 2 * te10Mode E0 omega beta ((Real.pi / 2) / omega) 0) := by
    rw [deriv_partialTime_te10Mode_eq, deriv_partialZ_te10Mode_eq]
    intro hcon
    exact hdisp (dispersion_of_algebraic _ _ _ _ _ hf0 hcon)
  exact not_sourceFree_of_modeEquation_failure (te10Profile a) (te10Mode E0 omega beta)
    (cutoffWavenumber a) c (contDiff_te10Profile a) (contDiff_te10Mode E0 omega beta)
    (te10Profile_profileEquation a) ((Real.pi / 2) / omega) (a / 2) 0 hax hmismatch

/-! ## F. Side-wall traces -/

/-- **PEC traces.** For a guide of positive widths `a` and `b`, at every time the TE10 fields
satisfy the PEC traces on the four side walls. -/
theorem te10_rectangularGuidePECTraces (a b E0 omega beta : ℝ) (ha : 0 < a) (hb : 0 < b)
    (t : ℝ) :
    rectangularGuidePECTraces a b (fieldAtTime (te10ElectricField a E0 omega beta) t)
      (fieldAtTime (te10MagneticField a E0 omega beta) t) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hkc_a := cutoffWavenumber_mul_self a ha0
  have hprof0 : te10Profile a 0 = 0 := by
    change Real.sin (cutoffWavenumber a * 0) = 0
    rw [mul_zero, Real.sin_zero]
  have hprofA : te10Profile a a = 0 := by
    change Real.sin (cutoffWavenumber a * a) = 0
    rw [hkc_a, Real.sin_pi]
  refine ⟨⟨ha, hb⟩, ?_, ?_, ?_, ?_⟩
  · intro y z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [hprof0, zero_mul, neg_zero]
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · simp only [normalMagneticOnXWall, fieldAtTime, te10MagneticField, separableMagneticField,
        Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hprof0, zero_mul, neg_zero]
  · intro y z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [hprofA, zero_mul, neg_zero]
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · simp only [normalMagneticOnXWall, fieldAtTime, te10MagneticField, separableMagneticField,
        Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hprofA, zero_mul, neg_zero]
  · intro x z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · simp only [normalMagneticOnYWall, fieldAtTime, te10MagneticField, separableMagneticField,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
  · intro x z _ _
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      · simp only [fieldAtTime, te10ElectricField, separableElectricField,
          Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · simp only [normalMagneticOnYWall, fieldAtTime, te10MagneticField, separableMagneticField,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]

/-! ## G. Nonvanishing -/

/-- Validation value: at `x = a / 2`, `t = z = 0` and any `y`, the electric component `E_y`
equals `E0`. -/
lemma te10ElectricField_center (a E0 omega beta : ℝ) (ha : a ≠ 0) (homega : omega ≠ 0)
    (y : ℝ) :
    te10ElectricField a E0 omega beta 0 (a / 2) y 0 1 = E0 := by
  have hkc2 := cutoffWavenumber_mul_half a ha
  rw [te10ElectricField_apply a E0 omega beta homega]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hkc2, Real.sin_pi_div_two,
    mul_zero, sub_zero, Real.cos_zero, mul_one]

/-- For a nonzero amplitude the TE10 electric field is not identically zero. -/
lemma te10ElectricField_ne_zero (a E0 omega beta : ℝ) (ha : 0 < a) (hE0 : E0 ≠ 0)
    (homega : 0 < omega) :
    te10ElectricField a E0 omega beta ≠ 0 := by
  intro hcon
  have h1 := te10ElectricField_center a E0 omega beta (ne_of_gt ha) (ne_of_gt homega) 0
  rw [hcon] at h1
  simp only [Pi.zero_apply] at h1
  exact hE0 h1.symm

/-! ## H. Cutoff -/

/-- **Cutoff.** A nonnegative propagation constant satisfying the dispersion relation exists
exactly when `ω ≥ c0 kc`. -/
theorem exists_nonneg_te10Dispersion_iff (c : SpeedOfLight) (a omega : ℝ) (ha : 0 < a)
    (homega : 0 < omega) :
    (∃ beta : ℝ, 0 ≤ beta ∧ te10Dispersion c a omega beta) ↔
      (c : ℝ) * cutoffWavenumber a ≤ omega := by
  constructor
  · rintro ⟨beta, hbeta, hdisp⟩
    have hc0 : 0 < (c : ℝ) := c.pos
    have hkc : 0 < cutoffWavenumber a := cutoffWavenumber_pos a ha
    have hsq := sq_le_of_dispersion c a omega beta hdisp
    have habs : |(c : ℝ) * cutoffWavenumber a| ≤ |omega| := sq_le_sq.mp hsq
    rw [abs_of_nonneg (mul_nonneg hc0.le hkc.le), abs_of_nonneg homega.le] at habs
    exact habs
  · intro hcut
    exact ⟨propagationConstant c a omega, Real.sqrt_nonneg _,
      te10Dispersion_propagationConstant c a omega ha hcut⟩

/-- At or above cutoff, the nonnegative solutions of the dispersion relation are exactly the
propagation constant. -/
lemma nonneg_te10Dispersion_iff_eq_propagationConstant (c : SpeedOfLight)
    (a omega beta : ℝ) (ha : 0 < a) (hcut : (c : ℝ) * cutoffWavenumber a ≤ omega) :
    (0 ≤ beta ∧ te10Dispersion c a omega beta) ↔ beta = propagationConstant c a omega := by
  constructor
  · rintro ⟨hbeta, hdisp⟩
    have hc0ne : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c.pos)
    have hdisp' : omega ^ 2 = (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 + beta ^ 2) := hdisp
    have h1 : omega ^ 2 / (c : ℝ) ^ 2 = cutoffWavenumber a ^ 2 + beta ^ 2 := by
      rw [hdisp', mul_div_cancel_left₀ _ hc0ne]
    have hβsq : beta ^ 2 = omega ^ 2 / (c : ℝ) ^ 2 - cutoffWavenumber a ^ 2 := by
      linear_combination -h1
    change beta = Real.sqrt (omega ^ 2 / (c : ℝ) ^ 2 - cutoffWavenumber a ^ 2)
    rw [← hβsq]
    exact (Real.sqrt_sq hbeta).symm
  · intro hβ
    rw [hβ]
    exact ⟨Real.sqrt_nonneg _,
      te10Dispersion_propagationConstant c a omega ha hcut⟩

/-- Cutoff equality: at `ω = c0 kc` the dispersion relation holds exactly for `β = 0`. -/
lemma te10Dispersion_at_cutoff_iff (c : SpeedOfLight) (a beta : ℝ) (ha : 0 < a) :
    te10Dispersion c a ((c : ℝ) * cutoffWavenumber a) beta ↔ beta = 0 := by
  have _ := ha
  constructor
  · intro h
    have h' : ((c : ℝ) * cutoffWavenumber a) ^ 2
        = (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 + beta ^ 2) := h
    have hc0ne : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c.pos)
    have hfactor : (c : ℝ) ^ 2 * beta ^ 2 = 0 := by linear_combination -h'
    rcases mul_eq_zero.mp hfactor with h0 | h0
    · exact absurd h0 hc0ne
    · exact sq_eq_zero_iff.mp h0
  · intro hβ
    change ((c : ℝ) * cutoffWavenumber a) ^ 2
      = (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 + beta ^ 2)
    rw [hβ]
    ring

/-- Below cutoff no real propagation constant satisfies the dispersion relation. -/
theorem not_exists_te10Dispersion_below_cutoff (c : SpeedOfLight) (a omega : ℝ)
    (ha : 0 < a) (homega : 0 < omega) (hbelow : omega < (c : ℝ) * cutoffWavenumber a) :
    ¬ ∃ beta : ℝ, te10Dispersion c a omega beta := by
  have _ := ha
  rintro ⟨beta, hdisp⟩
  have hsq_le := sq_le_of_dispersion c a omega beta hdisp
  have hsq_lt : omega ^ 2 < ((c : ℝ) * cutoffWavenumber a) ^ 2 :=
    pow_lt_pow_left₀ hbelow homega.le two_ne_zero
  linarith

/-! ## I. Main result -/

/-- **TE10 mode of a rectangular vacuum guide.** For guide widths `a, b > 0`, `E0 ≠ 0`, `ω > 0`,
`β ≥ 0` and the dispersion relation at speed `c`, the TE10 fields satisfy the source-free vacuum
Maxwell equations, the PEC traces on all four side walls at every time, the electric field is not
identically zero, the frequency is at or above cutoff, `β = 0` exactly at cutoff, and `β` is the
propagation constant. -/
theorem te10Mode_correct (c : SpeedOfLight) (a b E0 omega beta : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hE0 : E0 ≠ 0) (homega : 0 < omega) (hbeta : 0 ≤ beta)
    (hdisp : te10Dispersion c a omega beta) :
    sourceFreeVacuumMaxwell c (te10ElectricField a E0 omega beta)
        (te10MagneticField a E0 omega beta) ∧
      (∀ t : ℝ, rectangularGuidePECTraces a b
        (fieldAtTime (te10ElectricField a E0 omega beta) t)
        (fieldAtTime (te10MagneticField a E0 omega beta) t)) ∧
      te10ElectricField a E0 omega beta ≠ 0 ∧
      (c : ℝ) * cutoffWavenumber a ≤ omega ∧
      (beta = 0 ↔ omega = (c : ℝ) * cutoffWavenumber a) ∧
      beta = propagationConstant c a omega := by
  have hbulk := te10_sourceFreeVacuumMaxwell c a E0 omega beta hdisp
  have htraces : ∀ t : ℝ, rectangularGuidePECTraces a b
      (fieldAtTime (te10ElectricField a E0 omega beta) t)
      (fieldAtTime (te10MagneticField a E0 omega beta) t) :=
    fun t => te10_rectangularGuidePECTraces a b E0 omega beta ha hb t
  have hne := te10ElectricField_ne_zero a E0 omega beta ha hE0 homega
  have hcut : (c : ℝ) * cutoffWavenumber a ≤ omega :=
    (exists_nonneg_te10Dispersion_iff c a omega ha homega).mp ⟨beta, hbeta, hdisp⟩
  have hcutiff : beta = 0 ↔ omega = (c : ℝ) * cutoffWavenumber a := by
    constructor
    · intro hβ0
      have hsq : omega ^ 2 = ((c : ℝ) * cutoffWavenumber a) ^ 2 := by
        have hdisp' : omega ^ 2 = (c : ℝ) ^ 2 * (cutoffWavenumber a ^ 2 + beta ^ 2) := hdisp
        rw [hβ0] at hdisp'
        linear_combination hdisp'
      have hfactor : (omega - (c : ℝ) * cutoffWavenumber a) *
          (omega + (c : ℝ) * cutoffWavenumber a) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hfactor with h0 | h0
      · exact sub_eq_zero.mp h0
      · have hc0 : 0 < (c : ℝ) := c.pos
        have hkc : 0 < cutoffWavenumber a := cutoffWavenumber_pos a ha
        have hnn : 0 ≤ (c : ℝ) * cutoffWavenumber a := mul_nonneg hc0.le hkc.le
        linarith
    · intro hω
      rw [hω] at hdisp
      exact (te10Dispersion_at_cutoff_iff c a beta ha).mp hdisp
  have hprop : beta = propagationConstant c a omega :=
    (nonneg_te10Dispersion_iff_eq_propagationConstant c a omega beta ha hcut).mp
      ⟨hbeta, hdisp⟩
  exact ⟨hbulk, htraces, hne, hcut, hcutiff, hprop⟩

end PhyslibExt.Electromagnetism.VacuumTE10Mode
