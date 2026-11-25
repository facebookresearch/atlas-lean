/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
public import MathlibExt.Analysis.Numerical.PeriodicYeeResidual
public import MathlibExt.Analysis.Numerical.PeriodicYeeError
public import PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
public import Physlib.Electromagnetism.ThreeDimension.MaxwellEquations
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The periodic Yee scheme for a polarized vacuum Maxwell field

Error bound for the periodic Yee scheme applied to a one-dimensional polarized vacuum field.

## i. Overview

Free space `𝓕` has permittivity `ε₀ > 0`, permeability `μ₀ > 0` and speed of light
`c = 1 / sqrt (ε₀ * μ₀)`. Consider the one-dimensional configuration depending only on `t`
and `x` whose only nonzero components are `E_y` and `H_z`, with magnetic flux density
`B = μ₀ H`. If `(E, B)` satisfies the source-free vacuum Maxwell equations, the energy
coordinates `u = sqrt ε₀ * E_y` and `v = -sqrt μ₀ * H_z` satisfy the first-order wave system
`u_t = c * v_x`, `v_t = c * u_x`.

The physical periodic Yee update

`H^{n+1/2} = H^{n-1/2} - (dt / μ₀) D₋ E^n`, `E^{n+1} = E^n - (dt / ε₀) D₊ H^{n+1/2}`

is, in energy coordinates, exactly the generic periodic leapfrog step at speed `c`, and the
squared pair norm of the energy coordinates is twice the discrete electromagnetic energy
`h ∑ (ε₀ E² + μ₀ H²) / 2`. The generic leapfrog error theorem then bounds the normalized
electromagnetic error by

`sqrt ((1 + ρ) / (1 - ρ)) * (E₀ + T * sqrt L * (Mt * dt² + c * Mx * h²) / 6)`

for `n * dt ≤ T`, under the Courant bound `c * dt / h ≤ ρ < 1`, where
`Mt = max (sqrt ε₀ * MEt) (sqrt μ₀ * MHt)` and `Mx = max (sqrt ε₀ * MEx) (sqrt μ₀ * MHx)` are
built from the physical third-derivative bounds, `L = N * h`, and `E₀` is the normalized
initial mismatch (the `H` sample sits at the half time `-dt / 2`). The Maxwell hypothesis is
taken either in component form or as Physlib's extremum condition `IsExtrema 𝓕 0` of a
smooth electromagnetic potential whose fields have the polarized components.

The statements cover only this polarization in a homogeneous vacuum on a periodic domain:
no physical wall boundary, spatially varying, lossy or dispersive material, open radiation
boundary, floating-point arithmetic, continuum existence or solver convergence is claimed.

## ii. Key results

- `sourceFreeVacuumMaxwell_polarized_iff`: the component Maxwell equations for the
  polarized field reduce to `∂ₜ E_y = -(1 / ε₀) ∂ₓ H_z` and `∂ₜ H_z = -(1 / μ₀) ∂ₓ E_y`.
- `polarizedVacuumMaxwell_waveSystem`: the energy coordinates satisfy the wave system.
- `gridEnergyCoordinates_physicalYeeIterate`: the physical Yee iterates are the generic
  leapfrog iterates in energy coordinates.
- `pairNormSq_gridEnergyCoordinates`: the squared pair norm is twice the discrete energy.
- `periodicYeeMaxwell_error_le` and `periodicYeeMaxwell_error_le_of_exact_init`: the
  energy-coordinate error bounds.
- `sourceFreeVacuumMaxwell_of_isExtrema` and `periodicYeeMaxwell_error_le_of_isExtrema`: the
  component equations and the error bound from Physlib's extremum condition.
- `travellingWave_sourceFreeVacuumMaxwell`, `travellingWave_minusSign`,
  `travellingWave_isSpatiallyPeriodic` and `travellingWave_not_isSpatiallyPeriodic`: a
  polarized travelling wave, the sign of `v`, and the role of periodicity.

## iii. Table of contents

- A. The polarized field and its energy coordinates
- B. The physical Yee scheme in energy coordinates
- C. Derivative bounds in energy coordinates
- D. From Maxwell's equations to the normalized wave system
- E. The discrete scheme and energy in energy coordinates
- F. The normalized field is an admissible smooth periodic solution
- G. The energy-coordinate error bound
- H. The extremum form
- I. A polarized travelling wave and the sign of `v`

## iv. References

- K. S. Yee, *Numerical solution of initial boundary value problems involving Maxwell's
  equations in isotropic media*, IEEE Transactions on Antennas and Propagation 14 (1966),
  302–307.
- A. Taflove and S. C. Hagness, *Computational Electrodynamics: The Finite-Difference
  Time-Domain Method*, third edition, Artech House, 2005.
- J. D. Jackson, *Classical Electrodynamics*, third edition, Wiley, 1998.

-/

@[expose] public section

open scoped ContDiff

namespace PhyslibExt.Electromagnetism.Numerics.PeriodicYeeMaxwellBridge

open _root_.Electromagnetism
open PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
open MathlibExt.Analysis.Numerical.PeriodicYeeEnergy (pairNormSq pairNorm leapfrogIterate)
open MathlibExt.Analysis.Numerical.PeriodicYeeResidual (sampledU sampledV satisfiesWaveSystem
  isSpatiallyPeriodic isSmoothPeriodicSolution)
open MathlibExt.Analysis.Numerical.PeriodicYeeError (leapfrogPairError initialPairMismatch
  globalErrorBound)

/-! ## A. The polarized field and its energy coordinates -/

/-- Electric field of the polarized one-dimensional configuration, as a function of time and
three space coordinates: only `E_y` is nonzero and it depends on `t` and `x` only. -/
def polarizedElectricField (Ey : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  fun t x _y _z => ![0, Ey t x, 0]

/-- Magnetic flux density of the polarized configuration in vacuum, `B = μ₀ H` with only
`H_z` nonzero, depending on `t` and `x` only. -/
def polarizedMagneticField (𝓕 : FreeSpace) (Hz : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ :=
  fun t x _y _z => ![0, 0, 𝓕.μ₀ * Hz t x]

/-- Normalized electric energy coordinate `u = sqrt ε₀ * E_y`. -/
noncomputable def energyU (𝓕 : FreeSpace) (Ey : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => Real.sqrt 𝓕.ε₀ * Ey t x

/-- Normalized magnetic energy coordinate `v = -sqrt μ₀ * H_z`. -/
noncomputable def energyV (𝓕 : FreeSpace) (Hz : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => -(Real.sqrt 𝓕.μ₀ * Hz t x)

/-! ## B. The physical Yee scheme in energy coordinates -/

/-- Grid energy coordinates `(sqrt ε₀ • E, -sqrt μ₀ • H)` of grid fields `(E, H)`. -/
noncomputable def gridEnergyCoordinates {N : ℕ} (𝓕 : FreeSpace) (E H : Fin N → ℝ) :
    (Fin N → ℝ) × (Fin N → ℝ) :=
  (Real.sqrt 𝓕.ε₀ • E, (-Real.sqrt 𝓕.μ₀) • H)

/-- Discrete electromagnetic energy `h * ∑ j, (ε₀ * E j ^ 2 + μ₀ * H j ^ 2) / 2`. -/
noncomputable def gridFieldEnergy {N : ℕ} (𝓕 : FreeSpace) (h : ℝ) (E H : Fin N → ℝ) : ℝ :=
  h * ∑ j, (𝓕.ε₀ * E j ^ 2 + 𝓕.μ₀ * H j ^ 2) / 2

/-- One step of the physical periodic Yee update, returning `(E_new, H_new)`:
`H_new = H - (dt / μ₀) D₋ E`, then `E_new = E - (dt / ε₀) D₊ H_new`. -/
noncomputable def physicalYeeStep {N : ℕ} (𝓕 : FreeSpace) (h dt : ℝ) (E H : Fin N → ℝ) :
    (Fin N → ℝ) × (Fin N → ℝ) :=
  let HNew := H - (dt / 𝓕.μ₀) • dMinus h E
  (E - (dt / 𝓕.ε₀) • dPlus h HNew, HNew)

/-- Iterates of the physical periodic Yee update from initial grid fields `(E0, H0)`. -/
noncomputable def physicalYeeIterate {N : ℕ} (𝓕 : FreeSpace) (h dt : ℝ) (E0 H0 : Fin N → ℝ) :
    ℕ → (Fin N → ℝ) × (Fin N → ℝ)
  | 0 => (E0, H0)
  | n + 1 =>
      physicalYeeStep 𝓕 h dt (physicalYeeIterate 𝓕 h dt E0 H0 n).1
        (physicalYeeIterate 𝓕 h dt E0 H0 n).2

/-- Normalized electromagnetic error at step `n`: the pair norm, in energy coordinates, of
the difference between the staggered samples of `(E_y, H_z)` (the `H` sample at
`n * dt - dt / 2`, `j * h - h / 2`) and the `n`-th physical Yee iterate. -/
noncomputable def normalizedFieldError {N : ℕ} (𝓕 : FreeSpace) (Ey Hz : ℝ → ℝ → ℝ)
    (h dt : ℝ) (E0 H0 : Fin N → ℝ) (n : ℕ) : ℝ :=
  pairNorm h (Real.sqrt 𝓕.ε₀ • (sampledU Ey dt h n - (physicalYeeIterate 𝓕 h dt E0 H0 n).1))
    ((-Real.sqrt 𝓕.μ₀) • (sampledV Hz dt h n - (physicalYeeIterate 𝓕 h dt E0 H0 n).2))

/-- Normalized initial mismatch between the staggered samples at step `0` (the `H` sample at
the half time `-dt / 2`) and the initial grid fields. -/
noncomputable def normalizedInitialMismatch {N : ℕ} (𝓕 : FreeSpace) (Ey Hz : ℝ → ℝ → ℝ)
    (h dt : ℝ) (E0 H0 : Fin N → ℝ) : ℝ :=
  pairNorm h (Real.sqrt 𝓕.ε₀ • (sampledU Ey dt h 0 - E0))
    ((-Real.sqrt 𝓕.μ₀) • (sampledV Hz dt h 0 - H0))

/-! ## C. Derivative bounds in energy coordinates -/

/-- Third-derivative bounds of the physical fields: `MEt`, `MHt` on third time derivatives
of `E_y`, `H_z`, and `MEx`, `MHx` on their third space derivatives. -/
def hasFieldThirdDerivativeBounds (MEt MHt MEx MHx : ℝ) (Ey Hz : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x : ℝ, |iteratedDeriv 3 (fun s => Ey s x) t| ≤ MEt) ∧
    (∀ t x : ℝ, |iteratedDeriv 3 (fun s => Hz s x) t| ≤ MHt) ∧
    (∀ t x : ℝ, |iteratedDeriv 3 (fun y => Ey t y) x| ≤ MEx) ∧
    ∀ t x : ℝ, |iteratedDeriv 3 (fun y => Hz t y) x| ≤ MHx

/-- Time bound in energy coordinates: `max (sqrt ε₀ * MEt) (sqrt μ₀ * MHt)`. -/
noncomputable def energyTimeBound (𝓕 : FreeSpace) (MEt MHt : ℝ) : ℝ :=
  max (Real.sqrt 𝓕.ε₀ * MEt) (Real.sqrt 𝓕.μ₀ * MHt)

/-- Space bound in energy coordinates: `max (sqrt ε₀ * MEx) (sqrt μ₀ * MHx)`. -/
noncomputable def energySpaceBound (𝓕 : FreeSpace) (MEx MHx : ℝ) : ℝ :=
  max (Real.sqrt 𝓕.ε₀ * MEx) (Real.sqrt 𝓕.μ₀ * MHx)

/-! ## D. From Maxwell's equations to the normalized wave system -/

/-- For the polarized configuration, the source-free vacuum Maxwell equations at the
free-space speed of light are equivalent to the two component equations
`∂ₜ E_y = -(1 / ε₀) ∂ₓ H_z` and `∂ₜ H_z = -(1 / μ₀) ∂ₓ E_y`. -/
theorem sourceFreeVacuumMaxwell_polarized_iff (𝓕 : FreeSpace) (Ey Hz : ℝ → ℝ → ℝ) :
    sourceFreeVacuumMaxwell 𝓕.c (polarizedElectricField Ey) (polarizedMagneticField 𝓕 Hz) ↔
      ∀ t x : ℝ, deriv (fun s => Ey s x) t = -(1 / 𝓕.ε₀) * deriv (fun y => Hz t y) x ∧
        deriv (fun s => Hz s x) t = -(1 / 𝓕.μ₀) * deriv (fun y => Ey t y) x := by
  have hε := 𝓕.ε₀_pos.ne'
  have hμ := 𝓕.μ₀_pos.ne'
  have hc2 := FreeSpace.c_sq 𝓕
  simp only [sourceFreeVacuumMaxwell, spaceDivergence, spaceCurl, timeDerivativeComponent,
    polarizedElectricField, polarizedMagneticField]
  simp only [Fin.isValue, Matrix.cons_val_zero, deriv_const', Matrix.cons_val_one, add_zero,
    Matrix.cons_val, differentiableAt_const, deriv_fun_mul, zero_mul, mul_zero, sub_self,
    sub_zero, Nat.succ_eq_add_one, Nat.reduceAdd, neg_zero, deriv_const_mul_field',
    Matrix.vecCons_inj, and_true, true_and, zero_sub, forall_const, one_div, neg_mul]
  have hinv : (𝓕.c.val ^ 2)⁻¹ = 𝓕.ε₀ * 𝓕.μ₀ := by
    rw [show 𝓕.c.val = (𝓕.c : ℝ) from rfl, hc2]; field_simp
  simp only [hinv]
  refine forall_congr' fun t => forall_congr' fun x => ?_
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h2' : 𝓕.ε₀ * deriv (fun s => Ey s x) t = -deriv (fun y => Hz t y) x :=
        mul_left_cancel₀ hμ (by linear_combination (-1 : ℝ) * h2)
      field_simp
      linear_combination h2'
    · rw [h1]; field_simp
  · rintro ⟨h1, h2⟩
    constructor
    · rw [h2]; field_simp
    · rw [h1]; field_simp

/-- **Normalized wave system.** If the polarized configuration satisfies the source-free
vacuum Maxwell equations, then `u = sqrt ε₀ * E_y` and `v = -sqrt μ₀ * H_z` satisfy
`u_t = c * v_x` and `v_t = c * u_x` at the free-space speed of light `c`. -/
theorem polarizedVacuumMaxwell_waveSystem (𝓕 : FreeSpace) (Ey Hz : ℝ → ℝ → ℝ)
    (hmax : sourceFreeVacuumMaxwell 𝓕.c (polarizedElectricField Ey)
      (polarizedMagneticField 𝓕 Hz)) :
    satisfiesWaveSystem (𝓕.c : ℝ) (energyU 𝓕 Ey) (energyV 𝓕 Hz) := by
  have h := (sourceFreeVacuumMaxwell_polarized_iff 𝓕 Ey Hz).mp hmax
  have deriv_neg_mul : ∀ (b : ℝ) (f : ℝ → ℝ) (x : ℝ),
      deriv (fun y => -(b * f y)) x = -(b * deriv f x) := by
    intro b f x
    have e : (fun y => -(b * f y)) = fun y => (-b) * f y := by funext y; ring
    rw [e, deriv_const_mul_field']
    ring
  have c_eq : (𝓕.c : ℝ) = 1 / (√𝓕.ε₀ * √𝓕.μ₀) := by
    rw [FreeSpace.c_val, Real.sqrt_mul 𝓕.ε₀_pos.le]
  have hse := Real.sqrt_pos.mpr 𝓕.ε₀_pos
  have hsm := Real.sqrt_pos.mpr 𝓕.μ₀_pos
  have hε : 𝓕.ε₀ = √𝓕.ε₀ ^ 2 := (Real.sq_sqrt 𝓕.ε₀_pos.le).symm
  have hμ : 𝓕.μ₀ = √𝓕.μ₀ ^ 2 := (Real.sq_sqrt 𝓕.μ₀_pos.le).symm
  refine ⟨fun t x => ?_, fun t x => ?_⟩
  · simp only [energyU, energyV, deriv_const_mul_field', deriv_neg_mul]
    rw [(h t x).1, c_eq]
    set a := √𝓕.ε₀
    set b := √𝓕.μ₀
    rw [hε]
    field_simp
  · simp only [energyU, energyV, deriv_const_mul_field', deriv_neg_mul]
    rw [(h t x).2, c_eq]
    set a := √𝓕.ε₀
    set b := √𝓕.μ₀
    rw [hμ]
    field_simp

/-! ## E. The discrete scheme and energy in energy coordinates -/

/-- In energy coordinates, one physical Yee step is exactly one generic leapfrog step at
the free-space speed of light. -/
theorem gridEnergyCoordinates_physicalYeeStep {N : ℕ} (𝓕 : FreeSpace) (h dt : ℝ)
    (E H : Fin N → ℝ) :
    gridEnergyCoordinates 𝓕 (physicalYeeStep 𝓕 h dt E H).1 (physicalYeeStep 𝓕 h dt E H).2 =
      leapfrogStep h (𝓕.c : ℝ) dt (gridEnergyCoordinates 𝓕 E H).1
        (gridEnergyCoordinates 𝓕 E H).2 := by
  have hadj := dPlusAdjoint_eq_neg_dMinus (N := N) h
  have c_eq : (𝓕.c : ℝ) = 1 / (√𝓕.ε₀ * √𝓕.μ₀) := by
    rw [FreeSpace.c_val, Real.sqrt_mul 𝓕.ε₀_pos.le]
  have hse := Real.sqrt_pos.mpr 𝓕.ε₀_pos
  have hsm := Real.sqrt_pos.mpr 𝓕.μ₀_pos
  have hε : 𝓕.ε₀ = √𝓕.ε₀ ^ 2 := (Real.sq_sqrt 𝓕.ε₀_pos.le).symm
  have hμ : 𝓕.μ₀ = √𝓕.μ₀ ^ 2 := (Real.sq_sqrt 𝓕.μ₀_pos.le).symm
  simp only [gridEnergyCoordinates, physicalYeeStep, leapfrogStep, hadj, c_eq]
  set a := √𝓕.ε₀
  set b := √𝓕.μ₀
  rw [hε, hμ]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simp only [dPlus, dMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul]
    field_simp
    ring
  · simp only [dMinus, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    field_simp
    ring

/-- In energy coordinates, the physical Yee iterates are the generic leapfrog iterates from
the normalized initial data. -/
theorem gridEnergyCoordinates_physicalYeeIterate {N : ℕ} (𝓕 : FreeSpace) (h dt : ℝ)
    (E0 H0 : Fin N → ℝ) (n : ℕ) :
    gridEnergyCoordinates 𝓕 (physicalYeeIterate 𝓕 h dt E0 H0 n).1
        (physicalYeeIterate 𝓕 h dt E0 H0 n).2 =
      leapfrogIterate h (𝓕.c : ℝ) dt (Real.sqrt 𝓕.ε₀ • E0) ((-Real.sqrt 𝓕.μ₀) • H0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show physicalYeeIterate 𝓕 h dt E0 H0 (n + 1) =
      physicalYeeStep 𝓕 h dt (physicalYeeIterate 𝓕 h dt E0 H0 n).1
        (physicalYeeIterate 𝓕 h dt E0 H0 n).2 from rfl,
      gridEnergyCoordinates_physicalYeeStep 𝓕 h dt _ _, ih]
    rfl

/-- The squared pair norm of the energy coordinates is twice the discrete electromagnetic
energy. -/
theorem pairNormSq_gridEnergyCoordinates {N : ℕ} (𝓕 : FreeSpace) (h : ℝ) (E H : Fin N → ℝ) :
    pairNormSq h (gridEnergyCoordinates 𝓕 E H).1 (gridEnergyCoordinates 𝓕 E H).2 =
      2 * gridFieldEnergy 𝓕 h E H := by
  simp only [MathlibExt.Analysis.Numerical.PeriodicYeeEnergy.pairNormSq,
    MathlibExt.Analysis.Numerical.PeriodicYeeEnergy.weightedNormSq, weightedInner,
    gridEnergyCoordinates, gridFieldEnergy, Pi.smul_apply, smul_eq_mul]
  have hε := Real.sq_sqrt 𝓕.ε₀_pos.le
  have hμ := Real.sq_sqrt 𝓕.μ₀_pos.le
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have e1 : ∑ j, √𝓕.ε₀ * E j * (√𝓕.ε₀ * E j) = ∑ j, 𝓕.ε₀ * E j ^ 2 :=
    Finset.sum_congr rfl fun j _ => by
      rw [show √𝓕.ε₀ * E j * (√𝓕.ε₀ * E j) = √𝓕.ε₀ ^ 2 * E j ^ 2 by ring, hε]
  have e2 : ∑ j, -√𝓕.μ₀ * H j * (-√𝓕.μ₀ * H j) = ∑ j, 𝓕.μ₀ * H j ^ 2 :=
    Finset.sum_congr rfl fun j _ => by
      rw [show -√𝓕.μ₀ * H j * (-√𝓕.μ₀ * H j) = √𝓕.μ₀ ^ 2 * H j ^ 2 by ring, hμ]
  rw [e1, e2]
  ring

/-- The normalized error is the square root of twice the discrete electromagnetic energy of
the field error. -/
theorem normalizedFieldError_eq_sqrt_energy {N : ℕ} (𝓕 : FreeSpace) (Ey Hz : ℝ → ℝ → ℝ)
    (h dt : ℝ) (E0 H0 : Fin N → ℝ) (n : ℕ) :
    normalizedFieldError 𝓕 Ey Hz h dt E0 H0 n =
      Real.sqrt (2 * gridFieldEnergy 𝓕 h
        (sampledU Ey dt h n - (physicalYeeIterate 𝓕 h dt E0 H0 n).1)
        (sampledV Hz dt h n - (physicalYeeIterate 𝓕 h dt E0 H0 n).2)) := by
  rw [← pairNormSq_gridEnergyCoordinates]
  rfl

/-! ## F. The normalized field is an admissible smooth periodic solution -/

/-- A polarized vacuum Maxwell field that is spatially periodic, separately `C³` in each
argument and has the physical third-derivative bounds gives, in energy coordinates, a
smooth periodic solution of the wave system with the energy-coordinate bounds. -/
theorem polarizedVacuumMaxwell_isSmoothPeriodicSolution (𝓕 : FreeSpace)
    (L MEt MHt MEx MHx : ℝ) (Ey Hz : ℝ → ℝ → ℝ)
    (hmax : sourceFreeVacuumMaxwell 𝓕.c (polarizedElectricField Ey)
      (polarizedMagneticField 𝓕 Hz))
    (hper : isSpatiallyPeriodic L Ey Hz)
    (hEt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Ey t x))
    (hHt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Hz t x))
    (hEx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Ey t y))
    (hHx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Hz t y))
    (hbd : hasFieldThirdDerivativeBounds MEt MHt MEx MHx Ey Hz) :
    isSmoothPeriodicSolution L (𝓕.c : ℝ) (energyTimeBound 𝓕 MEt MHt)
      (energySpaceBound 𝓕 MEx MHx) (energyU 𝓕 Ey) (energyV 𝓕 Hz) := by
  have hse := Real.sqrt_nonneg 𝓕.ε₀
  have hsm := Real.sqrt_nonneg 𝓕.μ₀
  have hnegmul : ∀ (b : ℝ) (f : ℝ → ℝ),
      (fun y => -(b * f y)) = fun y => (-b) * f y := fun b f => by funext y; ring
  obtain ⟨b1, b2, b3, b4⟩ := hbd
  refine ⟨polarizedVacuumMaxwell_waveSystem 𝓕 Ey Hz hmax,
    ⟨fun t x => ?_, fun t x => ?_⟩, fun x => ?_, fun x => ?_, fun t => ?_, fun t => ?_,
    fun t x => ?_, fun t x => ?_, fun t x => ?_, fun t x => ?_⟩
  · simp only [energyU, hper.1 t x]
  · simp only [energyV, hper.2 t x]
  · exact contDiff_const.mul (hEt x)
  · exact (contDiff_const.mul (hHt x)).neg
  · exact contDiff_const.mul (hEx t)
  · exact (contDiff_const.mul (hHx t)).neg
  · simp only [energyU, energyTimeBound]
    rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_nonneg hse]
    exact le_trans (mul_le_mul_of_nonneg_left (b1 t x) hse) (le_max_left _ _)
  · simp only [energyV, energyTimeBound]
    rw [hnegmul, iteratedDeriv_const_mul_field, abs_mul, abs_neg, abs_of_nonneg hsm]
    exact le_trans (mul_le_mul_of_nonneg_left (b2 t x) hsm) (le_max_right _ _)
  · simp only [energyU, energySpaceBound]
    rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_nonneg hse]
    exact le_trans (mul_le_mul_of_nonneg_left (b3 t x) hse) (le_max_left _ _)
  · simp only [energyV, energySpaceBound]
    rw [hnegmul, iteratedDeriv_const_mul_field, abs_mul, abs_neg, abs_of_nonneg hsm]
    exact le_trans (mul_le_mul_of_nonneg_left (b4 t x) hsm) (le_max_right _ _)

/-! ## G. The energy-coordinate error bound -/

/-- **Periodic Yee error bound for the polarized vacuum Maxwell field.** On a periodic grid
of `N` cells of width `h` with `L = N * h`, under the Courant bound `c * dt / h ≤ ρ < 1` at
the free-space speed of light `c`, for every step `n` with `n * dt ≤ T`, the normalized
electromagnetic error of the physical Yee iterates is at most
`sqrt ((1 + ρ) / (1 - ρ)) * (E₀ + T * sqrt L * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 6)`, with
`E₀` the normalized initial mismatch and `Mt`, `Mx` the energy-coordinate bounds. -/
theorem periodicYeeMaxwell_error_le {N : ℕ} (hN : 0 < N) (𝓕 : FreeSpace)
    (h dt L MEt MHt MEx MHx rho T : ℝ) (hh : 0 < h) (hdt : 0 < dt)
    (hL : L = (N : ℝ) * h) (hr : (𝓕.c : ℝ) * dt / h ≤ rho) (hrho : rho < 1)
    (Ey Hz : ℝ → ℝ → ℝ)
    (hmax : sourceFreeVacuumMaxwell 𝓕.c (polarizedElectricField Ey)
      (polarizedMagneticField 𝓕 Hz))
    (hper : isSpatiallyPeriodic L Ey Hz)
    (hEt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Ey t x))
    (hHt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Hz t x))
    (hEx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Ey t y))
    (hHx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Hz t y))
    (hbd : hasFieldThirdDerivativeBounds MEt MHt MEx MHx Ey Hz)
    (E0 H0 : Fin N → ℝ) (n : ℕ) (hn : (n : ℝ) * dt ≤ T) :
    normalizedFieldError 𝓕 Ey Hz h dt E0 H0 n ≤
      globalErrorBound rho T L (𝓕.c : ℝ) (energyTimeBound 𝓕 MEt MHt)
        (energySpaceBound 𝓕 MEx MHx) dt h (normalizedInitialMismatch 𝓕 Ey Hz h dt E0 H0) := by
  have hsol := polarizedVacuumMaxwell_isSmoothPeriodicSolution 𝓕 L MEt MHt MEx MHx Ey Hz
    hmax hper hEt hHt hEx hHx hbd
  have hMt : 0 ≤ energyTimeBound 𝓕 MEt MHt :=
    le_trans (mul_nonneg (Real.sqrt_nonneg _) (le_trans (abs_nonneg _) (hbd.1 0 0)))
      (le_max_left _ _)
  have hMx : 0 ≤ energySpaceBound 𝓕 MEx MHx :=
    le_trans (mul_nonneg (Real.sqrt_nonneg _) (le_trans (abs_nonneg _) (hbd.2.2.1 0 0)))
      (le_max_left _ _)
  have hU : ∀ m, (sampledU (energyU 𝓕 Ey) dt h m : Fin N → ℝ) =
      Real.sqrt 𝓕.ε₀ • sampledU Ey dt h m := fun _ => rfl
  have hV : ∀ m, (sampledV (energyV 𝓕 Hz) dt h m : Fin N → ℝ) =
      (-Real.sqrt 𝓕.μ₀) • sampledV Hz dt h m := fun m => by
    funext j; simp [sampledV, energyV]
  have key := MathlibExt.Analysis.Numerical.PeriodicYeeError.leapfrogPairError_le hN h dt
    (𝓕.c : ℝ) L _ _ rho T hh hdt 𝓕.c.pos hL hMt hMx hr hrho _ _ hsol
    (Real.sqrt 𝓕.ε₀ • E0) ((-Real.sqrt 𝓕.μ₀) • H0) n hn
  have hErr : normalizedFieldError 𝓕 Ey Hz h dt E0 H0 n =
      leapfrogPairError (energyU 𝓕 Ey) (energyV 𝓕 Hz) h (𝓕.c : ℝ) dt
        (Real.sqrt 𝓕.ε₀ • E0) ((-Real.sqrt 𝓕.μ₀) • H0) n := by
    have hit := gridEnergyCoordinates_physicalYeeIterate 𝓕 h dt E0 H0 n
    simp only [leapfrogPairError, ← hit, gridEnergyCoordinates, hU, hV, ← smul_sub]
    rfl
  have hMis : normalizedInitialMismatch 𝓕 Ey Hz h dt E0 H0 =
      initialPairMismatch (energyU 𝓕 Ey) (energyV 𝓕 Hz) h dt
        (Real.sqrt 𝓕.ε₀ • E0) ((-Real.sqrt 𝓕.μ₀) • H0) := by
    simp only [initialPairMismatch, hU, hV, ← smul_sub]
    rfl
  rw [hErr, hMis]
  exact key

/-- Exact staggered initialization of both fields (the `H` data at the half time
`-dt / 2`) removes the mismatch term. -/
theorem periodicYeeMaxwell_error_le_of_exact_init {N : ℕ} (hN : 0 < N) (𝓕 : FreeSpace)
    (h dt L MEt MHt MEx MHx rho T : ℝ) (hh : 0 < h) (hdt : 0 < dt)
    (hL : L = (N : ℝ) * h) (hr : (𝓕.c : ℝ) * dt / h ≤ rho) (hrho : rho < 1)
    (Ey Hz : ℝ → ℝ → ℝ)
    (hmax : sourceFreeVacuumMaxwell 𝓕.c (polarizedElectricField Ey)
      (polarizedMagneticField 𝓕 Hz))
    (hper : isSpatiallyPeriodic L Ey Hz)
    (hEt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Ey t x))
    (hHt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Hz t x))
    (hEx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Ey t y))
    (hHx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Hz t y))
    (hbd : hasFieldThirdDerivativeBounds MEt MHt MEx MHx Ey Hz)
    (n : ℕ) (hn : (n : ℝ) * dt ≤ T) :
    normalizedFieldError (N := N) 𝓕 Ey Hz h dt (sampledU Ey dt h 0) (sampledV Hz dt h 0) n ≤
      Real.sqrt ((1 + rho) / (1 - rho)) *
        (T * Real.sqrt L * (energyTimeBound 𝓕 MEt MHt * dt ^ 2 +
          (𝓕.c : ℝ) * energySpaceBound 𝓕 MEx MHx * h ^ 2) / 6) := by
  have hsol := polarizedVacuumMaxwell_isSmoothPeriodicSolution 𝓕 L MEt MHt MEx MHx Ey Hz
    hmax hper hEt hHt hEx hHx hbd
  have hMt : 0 ≤ energyTimeBound 𝓕 MEt MHt :=
    le_trans (mul_nonneg (Real.sqrt_nonneg _) (le_trans (abs_nonneg _) (hbd.1 0 0)))
      (le_max_left _ _)
  have hMx : 0 ≤ energySpaceBound 𝓕 MEx MHx :=
    le_trans (mul_nonneg (Real.sqrt_nonneg _) (le_trans (abs_nonneg _) (hbd.2.2.1 0 0)))
      (le_max_left _ _)
  have hU : ∀ m, (sampledU (energyU 𝓕 Ey) dt h m : Fin N → ℝ) =
      Real.sqrt 𝓕.ε₀ • sampledU Ey dt h m := fun _ => rfl
  have hV : ∀ m, (sampledV (energyV 𝓕 Hz) dt h m : Fin N → ℝ) =
      (-Real.sqrt 𝓕.μ₀) • sampledV Hz dt h m := fun m => by
    funext j; simp [sampledV, energyV]
  have key := MathlibExt.Analysis.Numerical.PeriodicYeeError.leapfrogPairError_le_of_exact_init
    (N := N) hN h dt (𝓕.c : ℝ) L _ _ rho T hh hdt 𝓕.c.pos hL hMt hMx hr hrho _ _ hsol n hn
  have hErr : normalizedFieldError (N := N) 𝓕 Ey Hz h dt (sampledU Ey dt h 0)
      (sampledV Hz dt h 0) n =
      leapfrogPairError (N := N) (energyU 𝓕 Ey) (energyV 𝓕 Hz) h (𝓕.c : ℝ) dt
        (sampledU (energyU 𝓕 Ey) dt h 0) (sampledV (energyV 𝓕 Hz) dt h 0) n := by
    have hit := gridEnergyCoordinates_physicalYeeIterate (N := N) 𝓕 h dt (sampledU Ey dt h 0)
      (sampledV Hz dt h 0) n
    simp only [leapfrogPairError, hU 0, hV 0, ← hit, gridEnergyCoordinates, hU, hV, ← smul_sub]
    rfl
  rw [hErr]
  exact key

/-! ## H. The extremum form -/

/-- **Component Maxwell equations from the extremum condition.** If a smooth potential `A` is
an extremum of the free-space Lagrangian with zero current, and its canonical electric and
magnetic fields have components `FE` and `FB`, then `FE` and `FB` satisfy the source-free
vacuum Maxwell equations in component form at the free-space speed of light. -/
theorem sourceFreeVacuumMaxwell_of_isExtrema (𝓕 : FreeSpace) (A : ElectromagneticPotential)
    (hA : ContDiff ℝ ∞ A) (hext : A.IsExtrema 𝓕 0) (FE FB : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ)
    (hE : ∀ s q i, A.electricField 𝓕.c s q i = FE s.val (q 0) (q 1) (q 2) i)
    (hB : ∀ s q i, A.magneticField 𝓕.c s q i = FB s.val (q 0) (q 1) (q 2) i) :
    sourceFreeVacuumMaxwell 𝓕.c FE FB := by
  have hEd : Differentiable ℝ ↿(A.electricField 𝓕.c) :=
    (ElectromagneticPotential.electricField_contDiff (n := 1)
      (hA.of_le (by simp))).differentiable (by simp)
  have hBd : Differentiable ℝ ↿(A.magneticField 𝓕.c) := by
    rw [ElectromagneticPotential.magneticField_eq_magneticFieldMatrix A
      (hA.differentiable (by simp)), differentiable_euclidean]
    intro i
    exact (ElectromagneticPotential.magneticFieldMatrix_differentiable A
      (hA.of_le (by simp)) _).neg
  have hJ : ContDiff ℝ ∞ (0 : LorentzCurrentDensity) := contDiff_zero_fun
  have hμε : 𝓕.μ₀ * 𝓕.ε₀ = ((𝓕.c : ℝ) ^ 2)⁻¹ := by
    rw [FreeSpace.c_sq]
    simp [mul_comm]
  intro t x y z
  obtain ⟨dE, cE, tE⟩ := div_curl_deriv_eq_of_components _ FE hE hEd ⟨t⟩ ⟨![x, y, z]⟩
  obtain ⟨dB, cB, tB⟩ := div_curl_deriv_eq_of_components _ FB hB hBd ⟨t⟩ ⟨![x, y, z]⟩
  have gE := ThreeDimension.gaussLawElectric (𝓕 := 𝓕) A 0 ⟨t⟩ ⟨![x, y, z]⟩ hext hA hJ
  have gB := ThreeDimension.gaussLawMagnetic (𝓕 := 𝓕) A ⟨t⟩ ⟨![x, y, z]⟩ hA
  have far := ThreeDimension.faradayLaw (𝓕 := 𝓕) A ⟨t⟩ ⟨![x, y, z]⟩ hA
  have amp := ThreeDimension.ampereLaw (𝓕 := 𝓕) A 0 ⟨t⟩ ⟨![x, y, z]⟩ hext hA hJ
  simp only [LorentzCurrentDensity.chargeDensity_zero, Pi.zero_apply, zero_div] at gE
  have hfar : ∀ i, spaceCurl FE t x y z i = -timeDerivativeComponent FB t x y z i := by
    intro i
    have h := congrArg (fun v => v i) far
    simp only [PiLp.neg_apply] at h
    exact (cE i).symm.trans (h.trans (congrArg Neg.neg (tB i)))
  have hamp : ∀ i, spaceCurl FB t x y z i =
      ((𝓕.c : ℝ) ^ 2)⁻¹ * timeDerivativeComponent FE t x y z i := by
    intro i
    have h := congrArg (fun v => v i) amp
    simp only [LorentzCurrentDensity.currentDensity_zero, Pi.zero_apply, smul_zero, zero_add,
      PiLp.smul_apply, smul_eq_mul, ← mul_assoc, hμε] at h
    exact (cB i).symm.trans (h.trans (congrArg (((𝓕.c : ℝ) ^ 2)⁻¹ * ·) (tE i)))
  refine ⟨dE.symm.trans gE, dB.symm.trans gB, ?_, ?_⟩
  · funext i
    rw [hfar i]
    fin_cases i <;> rfl
  · funext i
    rw [hamp i]
    fin_cases i <;> rfl

/-- **Periodic Yee error bound from the extremum condition.** The bound of
`periodicYeeMaxwell_error_le` for a polarized field given as the canonical electric and
magnetic fields of a smooth potential that is an extremum of the free-space Lagrangian with
zero current. -/
theorem periodicYeeMaxwell_error_le_of_isExtrema {N : ℕ} (hN : 0 < N) (𝓕 : FreeSpace)
    (h dt L MEt MHt MEx MHx rho T : ℝ) (hh : 0 < h) (hdt : 0 < dt)
    (hL : L = (N : ℝ) * h) (hr : (𝓕.c : ℝ) * dt / h ≤ rho) (hrho : rho < 1)
    (A : ElectromagneticPotential) (hA : ContDiff ℝ ∞ A) (hext : A.IsExtrema 𝓕 0)
    (Ey Hz : ℝ → ℝ → ℝ)
    (hE : ∀ s q i, A.electricField 𝓕.c s q i =
      polarizedElectricField Ey s.val (q 0) (q 1) (q 2) i)
    (hB : ∀ s q i, A.magneticField 𝓕.c s q i =
      polarizedMagneticField 𝓕 Hz s.val (q 0) (q 1) (q 2) i)
    (hper : isSpatiallyPeriodic L Ey Hz)
    (hEt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Ey t x))
    (hHt : ∀ x : ℝ, ContDiff ℝ 3 (fun t => Hz t x))
    (hEx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Ey t y))
    (hHx : ∀ t : ℝ, ContDiff ℝ 3 (fun y => Hz t y))
    (hbd : hasFieldThirdDerivativeBounds MEt MHt MEx MHx Ey Hz)
    (E0 H0 : Fin N → ℝ) (n : ℕ) (hn : (n : ℝ) * dt ≤ T) :
    normalizedFieldError 𝓕 Ey Hz h dt E0 H0 n ≤
      globalErrorBound rho T L (𝓕.c : ℝ) (energyTimeBound 𝓕 MEt MHt)
        (energySpaceBound 𝓕 MEx MHx) dt h (normalizedInitialMismatch 𝓕 Ey Hz h dt E0 H0) :=
  periodicYeeMaxwell_error_le hN 𝓕 h dt L MEt MHt MEx MHx rho T hh hdt hL hr hrho Ey Hz
    (sourceFreeVacuumMaxwell_of_isExtrema 𝓕 A hA hext _ _ hE hB) hper hEt hHt hEx hHx hbd
    E0 H0 n hn

/-! ## I. A polarized travelling wave and the sign of `v` -/

/-- Travelling wave `E_y = A cos (k (x - c t))` at the free-space speed of light. -/
noncomputable def travellingWaveE (𝓕 : FreeSpace) (A k : ℝ) : ℝ → ℝ → ℝ :=
  fun t x => A * Real.cos (k * (x - (𝓕.c : ℝ) * t))

/-- Matching magnetic field `H_z = A sqrt (ε₀ / μ₀) cos (k (x - c t))` (vacuum impedance
`sqrt (μ₀ / ε₀)`). -/
noncomputable def travellingWaveH (𝓕 : FreeSpace) (A k : ℝ) : ℝ → ℝ → ℝ :=
  fun t x => A * Real.sqrt (𝓕.ε₀ / 𝓕.μ₀) * Real.cos (k * (x - (𝓕.c : ℝ) * t))

/-- Validation (positive): the travelling wave satisfies the source-free vacuum Maxwell
equations in the polarized configuration, and it is nonzero when `A ≠ 0`. -/
theorem travellingWave_sourceFreeVacuumMaxwell (𝓕 : FreeSpace) (A k : ℝ) :
    sourceFreeVacuumMaxwell 𝓕.c (polarizedElectricField (travellingWaveE 𝓕 A k))
        (polarizedMagneticField 𝓕 (travellingWaveH 𝓕 A k)) ∧
      (A ≠ 0 → travellingWaveE 𝓕 A k 0 0 ≠ 0) := by
  have hasDerivAt_wave_t : ∀ (A k c x t : ℝ), HasDerivAt (fun s => A * Real.cos (k * (x - c * s)))
      (A * (Real.sin (k * (x - c * t)) * (k * c))) t := by
    intro A k c x t
    have := ((((hasDerivAt_id' t).const_mul c).const_sub x).const_mul k).cos.const_mul A
    convert this using 1
    ring
  have hasDerivAt_wave_x : ∀ (A k c x t : ℝ), HasDerivAt (fun y => A * Real.cos (k * (y - c * t)))
      (-(A * (Real.sin (k * (x - c * t)) * k))) x := by
    intro A k c x t
    have := ((((hasDerivAt_id' x).sub_const (c * t)).const_mul k).cos).const_mul A
    convert this using 1
    ring
  have c_eq : (𝓕.c : ℝ) = 1 / (√𝓕.ε₀ * √𝓕.μ₀) := by
    rw [FreeSpace.c_val, Real.sqrt_mul 𝓕.ε₀_pos.le]
  refine ⟨(sourceFreeVacuumMaxwell_polarized_iff 𝓕 _ _).mpr fun t x => ?_,
    fun hA => by simpa [travellingWaveE] using hA⟩
  have hse := Real.sqrt_pos.mpr 𝓕.ε₀_pos
  have hsm := Real.sqrt_pos.mpr 𝓕.μ₀_pos
  have hε : 𝓕.ε₀ = √𝓕.ε₀ ^ 2 := (Real.sq_sqrt 𝓕.ε₀_pos.le).symm
  have hμ : 𝓕.μ₀ = √𝓕.μ₀ ^ 2 := (Real.sq_sqrt 𝓕.μ₀_pos.le).symm
  have hdiv : √(𝓕.ε₀ / 𝓕.μ₀) = √𝓕.ε₀ / √𝓕.μ₀ := Real.sqrt_div 𝓕.ε₀_pos.le _
  simp only [travellingWaveE, travellingWaveH]
  rw [(hasDerivAt_wave_t A k _ x t).deriv, (hasDerivAt_wave_x A k _ x t).deriv,
    (hasDerivAt_wave_t (A * √(𝓕.ε₀ / 𝓕.μ₀)) k _ x t).deriv,
    (hasDerivAt_wave_x (A * √(𝓕.ε₀ / 𝓕.μ₀)) k _ x t).deriv, hdiv, c_eq]
  set a := √𝓕.ε₀
  set b := √𝓕.μ₀
  rw [hε, hμ]
  constructor <;> field_simp

/-- Validation (sign of `v`): for the travelling wave the energy coordinates satisfy
`v = -u`, and the normalization with the opposite sign, `v' = +sqrt μ₀ * H_z`, violates the
wave system whenever `A ≠ 0` and `k ≠ 0`. -/
theorem travellingWave_minusSign (𝓕 : FreeSpace) (A k : ℝ) :
    energyV 𝓕 (travellingWaveH 𝓕 A k) = (fun t x => -energyU 𝓕 (travellingWaveE 𝓕 A k) t x) ∧
      (A ≠ 0 → k ≠ 0 →
        ¬ satisfiesWaveSystem (𝓕.c : ℝ) (energyU 𝓕 (travellingWaveE 𝓕 A k))
          (fun t x => Real.sqrt 𝓕.μ₀ * travellingWaveH 𝓕 A k t x)) := by
  have deriv_cos_t : ∀ (k c x t : ℝ),
      deriv (fun s => Real.cos (k * (x - c * s))) t = Real.sin (k * (x - c * t)) * (k * c) := by
    intro k c x t
    have := ((((hasDerivAt_id' t).const_mul c).const_sub x).const_mul k).cos
    rw [this.deriv]
    ring
  have deriv_cos_x : ∀ (k c x t : ℝ),
      deriv (fun y => Real.cos (k * (y - c * t))) x = -(Real.sin (k * (x - c * t)) * k) := by
    intro k c x t
    have := ((((hasDerivAt_id' x).sub_const (c * t)).const_mul k).cos)
    rw [this.deriv]
    ring
  have hse := Real.sqrt_pos.mpr 𝓕.ε₀_pos
  have hsm := Real.sqrt_pos.mpr 𝓕.μ₀_pos
  have hdiv : √(𝓕.ε₀ / 𝓕.μ₀) = √𝓕.ε₀ / √𝓕.μ₀ := Real.sqrt_div 𝓕.ε₀_pos.le _
  refine ⟨funext fun t => funext fun x => ?_, fun hA hk hw => ?_⟩
  · simp only [energyV, energyU, travellingWaveH, travellingWaveE, hdiv]
    field_simp
  · have h1 := hw.1 0 (Real.pi / 2 / k)
    simp only [energyU, travellingWaveH, travellingWaveE, deriv_const_mul_field', hdiv] at h1
    rw [deriv_cos_t, deriv_cos_x] at h1
    have hpi : k * (Real.pi / 2 / k - (𝓕.c : ℝ) * 0) = Real.pi / 2 := by
      field_simp; ring
    have hpi' : k * (Real.pi / 2 / k - 𝓕.c.val * 0) = Real.pi / 2 := hpi
    rw [hpi', Real.sin_pi_div_two] at h1
    have hc' : 0 < 𝓕.c.val := 𝓕.c.pos
    field_simp at h1
    have h0 : A * k * (√𝓕.ε₀ * 𝓕.c.val) = 0 := by linarith
    exact mul_ne_zero (mul_ne_zero hA hk) (mul_pos hse hc').ne' h0

/-- Validation (periodic interpretation): with wavenumber `k = 2 π m / L` the travelling
wave is spatially periodic with period `L`. -/
theorem travellingWave_isSpatiallyPeriodic (𝓕 : FreeSpace) (A L : ℝ) (m : ℤ) (hL : L ≠ 0) :
    isSpatiallyPeriodic L (travellingWaveE 𝓕 A (2 * Real.pi * m / L))
      (travellingWaveH 𝓕 A (2 * Real.pi * m / L)) := by
  have key : ∀ t x : ℝ, Real.cos (2 * Real.pi * m / L * (x + L - (𝓕.c : ℝ) * t)) =
      Real.cos (2 * Real.pi * m / L * (x - (𝓕.c : ℝ) * t)) := by
    intro t x
    have e : 2 * Real.pi * m / L * (x + L - (𝓕.c : ℝ) * t) =
        2 * Real.pi * m / L * (x - (𝓕.c : ℝ) * t) + (m : ℤ) * (2 * Real.pi) := by
      field_simp; ring
    rw [e, Real.cos_add_int_mul_two_pi]
  exact ⟨fun t x => by simp only [travellingWaveE]; rw [key],
    fun t x => by simp only [travellingWaveH]; rw [key]⟩

/-- Validation (boundary): periodicity is a genuine restriction. The unit travelling wave
with `k = 1` is not periodic with period `1`, so the bound says nothing about it. -/
theorem travellingWave_not_isSpatiallyPeriodic (𝓕 : FreeSpace) :
    ¬ isSpatiallyPeriodic 1 (travellingWaveE 𝓕 1 1) (travellingWaveH 𝓕 1 1) := by
  intro h
  have h0 := h.1 0 0
  simp only [travellingWaveE, mul_zero, sub_zero, zero_add, one_mul, Real.cos_zero] at h0
  have : Real.cos 1 < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [Real.pi_gt_three])
      (zero_lt_one : (0 : ℝ) < 1)
    simpa using this
  linarith

end PhyslibExt.Electromagnetism.Numerics.PeriodicYeeMaxwellBridge
