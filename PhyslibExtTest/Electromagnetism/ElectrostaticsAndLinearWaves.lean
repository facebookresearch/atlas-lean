/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves

/-!
# Tests for `PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves`

Concrete consumers of the electrostatics, plane-wave, interface, charge-sign,
and transport API, and an axiom audit of every production theorem.

## i. Overview

These are elaboration and non-vacuity checks at concrete values, not new
results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Electrostatics with `rho = 2`, `eps = 1`, `L = 3`
- B. Field energy
- C. Plane waves
- D. Fresnel coefficients with `n1 = 1`, `n2 = 3 / 2`
- E. Snell's law and mean-square field amplitude
- F. Carrier-charge sign
- G. Transport with `mu = 2`, `kB * T = 3`, `q = -1`
- H. Axiom audit

## iv. References

- `PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves`

## A. Electrostatics with `rho = 2`, `eps = 1`, `L = 3`
-/

@[expose] public section

open PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves

namespace PhyslibExtTest.Electromagnetism.ElectrostaticsAndLinearWaves

/-- The potential vanishes at `x = 0`. -/
example : uniformChargePotential 2 1 3 0 = 0 :=
  uniformChargePotential_zero 2 1 3

/-- The potential vanishes at `x = L = 3`. -/
example : uniformChargePotential 2 1 3 3 = 0 :=
  uniformChargePotential_L 2 1 3

/-- Discrete Poisson equation at `x = 1`, `h = 1`: second difference `-2`. -/
example : uniformChargePotential 2 1 3 (1 + 1) -
    2 * uniformChargePotential 2 1 3 1 +
    uniformChargePotential 2 1 3 (1 - 1) = -2 := by
  rw [poisson_secondDifference one_ne_zero]
  norm_num

/-- Discrete Gauss law: `E 3 - E 0 = 6`. -/
example : uniformChargeField 2 1 3 3 - uniformChargeField 2 1 3 0 = 6 := by
  rw [gauss_1d one_ne_zero]
  norm_num

/-- The potential at the midpoint `x = 3 / 2` is `9 / 4`. -/
example : uniformChargePotential 2 1 3 (3 / 2) = 9 / 4 := by
  norm_num [uniformChargePotential]

/-! ## B. Field energy -/

/-- `fieldEnergyDensity 1 3 = 9 / 2`, from the definition. -/
example : fieldEnergyDensity 1 3 = 9 / 2 := by
  norm_num [fieldEnergyDensity]

/-! ## C. Plane waves -/

/-- Discrete wave equation with `k = 2`, `c = 3`, `omega = c * k = 6`. -/
example (E0 x t h : ℝ) :
    planeWave E0 2 6 x (t + h / 3) - 2 * planeWave E0 2 6 x t +
      planeWave E0 2 6 x (t - h / 3) =
      planeWave E0 2 6 (x + h) t - 2 * planeWave E0 2 6 x t +
        planeWave E0 2 6 (x - h) t :=
  planeWave_discreteWaveEquation (by norm_num) (by norm_num)

/-! ## D. Fresnel coefficients with `n1 = 1`, `n2 = 3 / 2` -/

/-- Reflection coefficient `R = -1 / 5`. -/
example : fresnelR 1 (3 / 2) = -1 / 5 := by
  norm_num [fresnelR]

/-- Transmission coefficient `T = 4 / 5`. -/
example : fresnelT 1 (3 / 2) = 4 / 5 := by
  norm_num [fresnelT]

/-- Energy conservation at this interface, via `fresnel_energy`. -/
example : fresnelR 1 (3 / 2) ^ 2 + (3 / 2 / 1) * fresnelT 1 (3 / 2) ^ 2 = 1 :=
  fresnel_energy (by norm_num) (by norm_num)

/-! ## E. Snell's law and mean-square field amplitude -/

/-- Snell's law at normal incidence for `n1 = 1`, `n2 = 3 / 2`. -/
example : snell 1 (3 / 2) 0 0 :=
  snell_normal 1 (3 / 2)

/-- `meanSquareAmplitude 3 = 9 / 2`, a squared field, not an SI energy flux. -/
example : meanSquareAmplitude 3 = 9 / 2 := by
  norm_num [meanSquareAmplitude]

/-- The mean-square field amplitude ignores the amplitude sign. -/
example : meanSquareAmplitude (-3) = 9 / 2 := by
  norm_num [meanSquareAmplitude]

/-- Zero field amplitude has zero mean square. -/
example : meanSquareAmplitude 0 = 0 := by
  norm_num [meanSquareAmplitude]

/-- Mean-square field amplitude is nonnegative, including at zero. -/
example : 0 ≤ meanSquareAmplitude 0 :=
  meanSquareAmplitude_nonneg 0

/-- A negative scale factor also scales the mean square quadratically. -/
example : meanSquareAmplitude ((-2) * 3) = (-2 : ℝ) ^ 2 * meanSquareAmplitude 3 :=
  meanSquareAmplitude_smul (-2) 3

/-! ## F. Carrier-charge sign -/

/-- A positive charge has sign `+1`. -/
example : Real.sign 1 = 1 :=
  Real.sign_of_pos (by norm_num)

/-- A negative charge has sign `-1`. -/
example : Real.sign (-1) = -1 :=
  Real.sign_of_neg (by norm_num)

/-- Neutral charge has sign zero, not `-1`. -/
example : Real.sign 0 = 0 :=
  Real.sign_zero

/-- The sign convention recovers `q = 2`. -/
example : Real.sign 2 * |(2 : ℝ)| = 2 :=
  chargeSign_mul_abs 2

/-- The sign convention recovers `q = -2`. -/
example : Real.sign (-2) * |(-2 : ℝ)| = -2 :=
  chargeSign_mul_abs (-2)

/-- Charge reconstruction also holds at neutral charge. -/
example : Real.sign 0 * |(0 : ℝ)| = 0 :=
  chargeSign_mul_abs 0

/-! ## G. Transport with `mu = 2`, `kB * T = 3`, `q = -1` -/

/-- With `mu = 2`, `kB = 3`, `T = 1`, and `q = -1` (so `|q| = 1`), `D = 6`. -/
example : diffusionCoeff 2 3 1 (-1) = 6 := by
  norm_num [diffusionCoeff]

/-- The Einstein relation at the same point. -/
example : diffusionCoeff 2 3 1 (-1) / 2 = 3 * 1 / |(-1 : ℝ)| :=
  einstein_ratio (by norm_num) (by norm_num)

/-- The Einstein relation at the same point evaluates to `D / mu = 3`. -/
example : diffusionCoeff 2 3 1 (-1) / 2 = 3 :=
  (einstein_ratio (by norm_num) (by norm_num)).trans (by norm_num)

/-- Two carriers `(n, q, mu) = (1, 1, 2), (1, -1, 3)`: `sigma = 2 + 3 = 5`. -/
example : conductivityTwoCarrier 1 1 2 1 (-1) 3 = 5 := by
  norm_num [conductivityTwoCarrier, conductivity]

end PhyslibExtTest.Electromagnetism.ElectrostaticsAndLinearWaves

/-! ## H. Axiom audit -/

#print axioms uniformChargePotential_zero
#print axioms uniformChargePotential_L
#print axioms poisson_secondDifference
#print axioms gauss_1d
#print axioms fieldEnergyDensity_nonneg
#print axioms planeWave_secondDifference_space
#print axioms planeWave_secondDifference_time
#print axioms planeWave_discreteWaveEquation
#print axioms fresnel_energy
#print axioms snell_normal
#print axioms meanSquareAmplitude_nonneg
#print axioms meanSquareAmplitude_smul
#print axioms chargeSign_mul_abs
#print axioms einstein_ratio
#print axioms conductivityTwoCarrier_eq_sum
#print axioms conductivity_nonneg
