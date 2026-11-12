/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Electrostatics, electromagnetic fields, and linear-wave interfaces

Explicit SI models for a uniformly charged interval, plane waves, a lossless
normal-incidence interface, and dilute-carrier transport, with their algebraic
consequences.

## i. Overview

Electrostatic and Maxwell dynamics and material constitutive laws are physical
hypotheses; the results here are mathematical consequences of explicit,
declared formulas. All formulas are SI. `eps` is the absolute permittivity,
`n1` and `n2` are dimensionless refractive indices, and all three are declared
medium parameters. Charge sign, relative versus absolute permittivity, and
field amplitude versus intensity remain distinct.

- Electrostatics: on `[0, L]` with uniform charge density `rho`, the potential
  `rho / (2 * eps) * x * (L - x)` vanishes at both ends; for `eps ≠ 0`, its
  second difference is `-(rho / eps) * h ^ 2` and the explicit field formula
  satisfies `E L - E 0 = rho * L / eps`. Everything is an explicit polynomial,
  so no regularity hypotheses are needed, and derivatives are not formalized.
- Plane waves: `E0 * cos (k * x - omega * t)` is a declared model in Maxwell
  notation. The wave equation is checked in second-difference form, not via
  `deriv`: with `omega = c * k` and `c ≠ 0`, the time step `h / c` matches the
  space step `h`.
- Interface: the Fresnel coefficients and Snell's law are declared interface
  formulas (boundary-condition consequences in the textbook model), not
  derived from Maxwell's equations. At normal incidence the s and p
  polarizations coincide; no oblique-incidence s/p formulas are claimed.
  `intensity` omits the medium-dependent SI prefactor, whose ratio across the
  interface is the factor `n2 / n1` in `fresnel_energy`.
- Transport: the carrier sign is carried by `q` alone (`chargeSign q`), and
  `|q|` enters the Einstein relation `D = mu * kB * T / |q|` (for `q ≠ 0`) and
  the dilute independent-carrier conductivity `n * |q| * mu`. With this fixed
  sign convention the mobility `mu` has the same sign for either carrier, and
  `sigma ≥ 0` when `n ≥ 0` and `mu ≥ 0`.

The module depends only on Mathlib. It does not import Physlib's free-space
Maxwell module, whose stated scope excludes integral formulations, boundary
conditions, and constitutive laws for material media, so the medium and
interface model here is declared rather than derived from it. Constitutive-law
derivations, magnetic materials, semiconductor band structure, nonuniform
charge, and nonplanar geometry are out of scope.

## ii. Key results

- `uniformChargePotential_zero`, `uniformChargePotential_L`: the potential
  vanishes at `x = 0` and `x = L`.
- `poisson_secondDifference`: the discrete Poisson equation.
- `gauss_1d`: the discrete Gauss law in 1D.
- `fieldEnergyDensity_nonneg`: the field-energy density is nonnegative.
- `planeWave_secondDifference_space`, `planeWave_secondDifference_time`,
  `planeWave_discreteWaveEquation`: the discrete wave equation.
- `fresnel_energy`: lossless energy conservation
  `R ^ 2 + (n2 / n1) * T ^ 2 = 1`.
- `snell_normal`: Snell's law at normal incidence.
- `intensity_nonneg`, `intensity_smul`: intensity is nonnegative and
  quadratic in the amplitude.
- `chargeSign_mul_abs`: `chargeSign q * |q| = q` for `q ≠ 0`.
- `einstein_ratio`: the Einstein relation `D / mu = kB * T / |q|`.
- `conductivityTwoCarrier_eq_sum`, `conductivity_nonneg`: two-carrier
  additivity and nonnegativity of the conductivity.

## iii. Table of contents

- A. Declared models and their consequences

## iv. References

- Roadmap R12, module MF16, targets MF16.1–MF16.5; the transport bridge
  MF16.5 is shared with CH55, MS19, and MS38.
- Mathlib's `Real.cos_add` and `Real.cos_sub`, for the plane-wave second
  differences.
- Physlib's `Physlib.Electromagnetism.ThreeDimension.MaxwellEquations`,
  section "A.3. Current scope", for the free-space scope; not imported.

## A. Declared models and their consequences
-/

@[expose] public section

noncomputable section

namespace PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves

/-- Electrostatic potential (SI) for uniform charge density `rho`, absolute
permittivity `eps`, on `[0, L]`, with `φ 0 = φ L = 0`. -/
noncomputable def uniformChargePotential (rho eps L : ℝ) (x : ℝ) : ℝ :=
  rho / (2 * eps) * x * (L - x)

/-- Electric field `E = -φ'` for `uniformChargePotential`, as an explicit formula. -/
noncomputable def uniformChargeField (rho eps L : ℝ) (x : ℝ) : ℝ :=
  rho / (2 * eps) * (2 * x - L)

/-- Field-energy density `u = eps / 2 * E ^ 2`. -/
noncomputable def fieldEnergyDensity (eps E : ℝ) : ℝ := eps / 2 * E ^ 2

/-- Plane wave `E0 * cos (k * x - omega * t)` (declared model, Maxwell notation). -/
noncomputable def planeWave (E0 k omega : ℝ) (x t : ℝ) : ℝ :=
  E0 * Real.cos (k * x - omega * t)

/-- Normal-incidence amplitude reflection coefficient `(n1 - n2) / (n1 + n2)`. -/
noncomputable def fresnelR (n1 n2 : ℝ) : ℝ := (n1 - n2) / (n1 + n2)

/-- Normal-incidence amplitude transmission coefficient `2 * n1 / (n1 + n2)`. -/
noncomputable def fresnelT (n1 n2 : ℝ) : ℝ := 2 * n1 / (n1 + n2)

/-- Snell's law as a relation (phase-matching form). -/
def snell (n1 n2 theta1 theta2 : ℝ) : Prop := n1 * Real.sin theta1 = n2 * Real.sin theta2

/-- Time-averaged intensity, proportional to amplitude squared. -/
noncomputable def intensity (E0 : ℝ) : ℝ := E0 ^ 2 / 2

/-- Carrier-charge sign convention: `+1` for positive, `-1` for negative charge. -/
noncomputable def chargeSign (q : ℝ) : ℝ := if 0 < q then 1 else -1

/-- Diffusion coefficient `D = mu * kB * T / |q|` (Einstein relation, solved for `D`). -/
noncomputable def diffusionCoeff (mu kB T q : ℝ) : ℝ := mu * kB * T / |q|

/-- Dilute independent-carrier conductivity `sigma = n * |q| * mu`. -/
noncomputable def conductivity (n q mu : ℝ) : ℝ := n * |q| * mu

/-- Two-carrier conductivity: sum of the independent single-carrier conductivities. -/
noncomputable def conductivityTwoCarrier (n1 q1 mu1 n2 q2 mu2 : ℝ) : ℝ :=
  conductivity n1 q1 mu1 + conductivity n2 q2 mu2

/-- Potential vanishes at both ends of `[0, L]`. -/
theorem uniformChargePotential_zero (rho eps L : ℝ) :
    uniformChargePotential rho eps L 0 = 0 := by
  simp [uniformChargePotential]

/-- Potential vanishes at both ends of `[0, L]`. -/
theorem uniformChargePotential_L (rho eps L : ℝ) :
    uniformChargePotential rho eps L L = 0 := by
  simp [uniformChargePotential]

/-- Discrete Poisson equation: the second difference of the potential is
`-(rho / eps) * h ^ 2`. -/
theorem poisson_secondDifference {rho eps L x h : ℝ} (heps : eps ≠ 0) :
    uniformChargePotential rho eps L (x + h) - 2 * uniformChargePotential rho eps L x +
      uniformChargePotential rho eps L (x - h) = -(rho / eps) * h ^ 2 := by
  unfold uniformChargePotential
  field_simp
  ring

/-- Discrete Gauss law in 1D: `E L - E 0 = rho * L / eps`. -/
theorem gauss_1d {rho eps L : ℝ} (heps : eps ≠ 0) :
    uniformChargeField rho eps L L - uniformChargeField rho eps L 0 = rho * L / eps := by
  unfold uniformChargeField
  field_simp
  ring

/-- Field-energy density is nonnegative for `eps ≥ 0`. -/
theorem fieldEnergyDensity_nonneg {eps E : ℝ} (heps : 0 ≤ eps) :
    0 ≤ fieldEnergyDensity eps E := by
  unfold fieldEnergyDensity
  positivity

/-- Second difference of the plane wave in space. -/
theorem planeWave_secondDifference_space (E0 k omega x t h : ℝ) :
    planeWave E0 k omega (x + h) t - 2 * planeWave E0 k omega x t +
      planeWave E0 k omega (x - h) t =
      2 * (Real.cos (k * h) - 1) * planeWave E0 k omega x t := by
  have hfwd : k * (x + h) - omega * t = (k * x - omega * t) + k * h := by ring
  have hbwd : k * (x - h) - omega * t = (k * x - omega * t) - k * h := by ring
  unfold planeWave
  rw [hfwd, hbwd, Real.cos_add (k * x - omega * t) (k * h),
    Real.cos_sub (k * x - omega * t) (k * h)]
  ring

/-- Second difference of the plane wave in time. -/
theorem planeWave_secondDifference_time (E0 k omega x t tau : ℝ) :
    planeWave E0 k omega x (t + tau) - 2 * planeWave E0 k omega x t +
      planeWave E0 k omega x (t - tau) =
      2 * (Real.cos (omega * tau) - 1) * planeWave E0 k omega x t := by
  have hfwd :
      k * x - omega * (t + tau) = (k * x - omega * t) - omega * tau := by ring
  have hbwd :
      k * x - omega * (t - tau) = (k * x - omega * t) + omega * tau := by ring
  unfold planeWave
  rw [hfwd, hbwd, Real.cos_sub (k * x - omega * t) (omega * tau),
    Real.cos_add (k * x - omega * t) (omega * tau)]
  ring

/-- Discrete wave equation: with `omega = c * k`, the time second difference
with step `h / c` equals the space second difference with step `h`. -/
theorem planeWave_discreteWaveEquation {E0 k omega c x t h : ℝ} (hc : c ≠ 0)
    (homega : omega = c * k) :
    planeWave E0 k omega x (t + h / c) - 2 * planeWave E0 k omega x t +
      planeWave E0 k omega x (t - h / c) =
      planeWave E0 k omega (x + h) t - 2 * planeWave E0 k omega x t +
        planeWave E0 k omega (x - h) t := by
  have hstep : omega * (h / c) = k * h := by
    rw [homega]
    field_simp
  rw [planeWave_secondDifference_time, planeWave_secondDifference_space, hstep]

/-- Lossless normal-incidence energy conservation: `R ^ 2 + (n2 / n1) * T ^ 2 = 1`. -/
theorem fresnel_energy {n1 n2 : ℝ} (hn1 : 0 < n1) (hn2 : 0 < n2) :
    fresnelR n1 n2 ^ 2 + (n2 / n1) * fresnelT n1 n2 ^ 2 = 1 := by
  have hn1' : n1 ≠ 0 := hn1.ne'
  have hsum : n1 + n2 ≠ 0 := (add_pos hn1 hn2).ne'
  unfold fresnelR fresnelT
  field_simp
  ring

/-- Snell's law holds at normal incidence. -/
theorem snell_normal (n1 n2 : ℝ) : snell n1 n2 0 0 := by
  simp [snell]

/-- Intensity is nonnegative. -/
theorem intensity_nonneg (E0 : ℝ) : 0 ≤ intensity E0 := by
  unfold intensity
  positivity

/-- Scaling the amplitude by `c` scales the intensity by `c ^ 2`. -/
theorem intensity_smul (c E0 : ℝ) : intensity (c * E0) = c ^ 2 * intensity E0 := by
  unfold intensity
  ring

/-- The sign convention recovers the charge: `chargeSign q * |q| = q`. -/
theorem chargeSign_mul_abs {q : ℝ} (hq : q ≠ 0) : chargeSign q * |q| = q := by
  unfold chargeSign
  rcases hq.lt_or_gt with hneg | hpos
  · rw [ite_eq_right (lt_asymm hneg), abs_of_neg hneg, neg_one_mul, neg_neg]
  · rw [ite_eq_left hpos, abs_of_pos hpos, one_mul]

/-- Einstein relation in ratio form: `D / mu = kB * T / |q|`. -/
theorem einstein_ratio {mu kB T q : ℝ} (hmu : mu ≠ 0) (hq : q ≠ 0) :
    diffusionCoeff mu kB T q / mu = kB * T / |q| := by
  have habs : |q| ≠ 0 := abs_ne_zero.mpr hq
  rw [div_eq_div_iff hmu habs, diffusionCoeff, div_mul_cancel₀ _ habs]
  ring

/-- Two-carrier conductivity is the sum of the single-carrier conductivities. -/
theorem conductivityTwoCarrier_eq_sum (n1 q1 mu1 n2 q2 mu2 : ℝ) :
    conductivityTwoCarrier n1 q1 mu1 n2 q2 mu2 =
      conductivity n1 q1 mu1 + conductivity n2 q2 mu2 := by
  rfl

/-- Conductivity is nonnegative for `n ≥ 0` and `mu ≥ 0`. -/
theorem conductivity_nonneg {n q mu : ℝ} (hn : 0 ≤ n) (hmu : 0 ≤ mu) :
    0 ≤ conductivity n q mu := by
  unfold conductivity
  positivity

end PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves
