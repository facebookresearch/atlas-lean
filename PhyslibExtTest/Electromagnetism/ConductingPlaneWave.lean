/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Electromagnetism.ConductingPlaneWave

/-!
# Tests for `PhyslibExt.Electromagnetism.ConductingPlaneWave`

Concrete consumers of the conducting plane-wave API, at unit
parameters and at a positive-conductivity point.

## i. Overview

These are elaboration and non-vacuity checks at concrete values, not
new results. At unit parameters with zero conductivity the
attenuation is `0`, the phase constant is the lossless wavenumber
`1`, and the propagation constant is `Complex.I`; the squared
equation then reads `Complex.I ^ 2 = -1`. A positive-conductivity
point exercises the skin-depth and travelling-wave consequences.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Lossless unit parameters with `epsilon = mu = omega = 1`, `sigma = 0`
- B. Positive conductivity with `epsilon = mu = omega = sigma = 1`
- C. Axiom audit

## iv. References

- `PhyslibExt.Electromagnetism.ConductingPlaneWave`

## A. Lossless unit parameters with `epsilon = mu = omega = 1`, `sigma = 0`
-/

@[expose] public section

open PhyslibExt.Electromagnetism.ConductingPlaneWave

namespace PhyslibExtTest.Electromagnetism.ConductingPlaneWave

/-- No attenuation at unit parameters with `sigma = 0`. -/
example : attenuationConstant 1 1 1 0 = 0 :=
  attenuationConstant_zero_sigma 1 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- The phase constant at unit parameters with `sigma = 0` is `1`. -/
example : phaseConstant 1 1 1 0 = 1 := by
  rw [phaseConstant_zero_sigma 1 1 1 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The propagation constant at unit parameters with `sigma = 0` is
purely imaginary. -/
example : propagationConstant 1 1 1 0 = Complex.I := by
  rw [propagationConstant_zero_sigma 1 1 1 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The squared equation at unit parameters with `sigma = 0`. -/
example : satisfiesDispersionEquation 1 1 1 0 (propagationConstant 1 1 1 0) :=
  propagationConstant_sq 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The squared equation written out at unit parameters: `Complex.I ^ 2 = -1`. -/
example : (propagationConstant 1 1 1 0) ^ 2 = -1 := by
  rw [propagationConstant_sq_eq 1 1 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  simp

/-- The bundled verification at unit parameters with `sigma = 0`. -/
example : satisfiesDispersionEquation 1 1 1 0 (propagationConstant 1 1 1 0) ∧
    0 ≤ attenuationConstant 1 1 1 0 ∧ 0 < phaseConstant 1 1 1 0 :=
  dispersion_verification 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The real plane wave at the unit wavenumber is the real part of
the conjugate of the forward phasor, at `E0 = 2`, `x = 1`, `t = 0`. -/
example : PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave
      2 (phaseConstant 1 1 1 0) 1 1 0 =
    (Complex.exp (Complex.I *
      ((phaseConstant 1 1 1 0 * 1 - 1 * 0 : ℝ) : ℂ)) * (2 : ℂ)).re :=
  planeWave_eq_re_phasor_at_zero_sigma 2 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) 1 0

/-- The real plane wave at the unit wavenumber is the real part of
the forward phasor of the declared convention, at `E0 = 2`, `x = 1`,
`t = 2`. -/
example : PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave
      2 (phaseConstant 1 1 1 0) 1 1 2 =
    (Complex.exp (Complex.I * ((1 * 2 : ℝ) : ℂ)) *
      Complex.exp (-propagationConstant 1 1 1 0 * ((1 : ℝ) : ℂ)) * (2 : ℂ)).re :=
  planeWave_eq_re_forward_phasor_at_zero_sigma 2 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) 1 2

/-! ## B. Positive conductivity with `epsilon = mu = omega = sigma = 1` -/

/-- Positive attenuation at `sigma = 1`. -/
example : 0 < attenuationConstant 1 1 1 1 :=
  attenuationConstant_pos_of_sigma_pos 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The skin depth at `sigma = 1` is positive and reciprocal to the
attenuation. -/
example : 0 < skinDepth 1 1 1 1 ∧
    attenuationConstant 1 1 1 1 * skinDepth 1 1 1 1 = 1 :=
  skinDepth_pos_and_mul_eq_one 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- The opposite root at `sigma = 1` is not the forward root. -/
example : (-propagationConstant 1 1 1 1).re ≤ 0 ∧
    (-propagationConstant 1 1 1 1).im < 0 :=
  neg_propagationConstant_not_forward 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- The opposite-sign equation at `sigma = 1` differs from the stated
equation. -/
example : (-(1 ^ 2 * 1 * 1 : ℝ) : ℂ) - Complex.I * ((1 * 1 * 1 : ℝ) : ℂ) ≠
    (-(1 ^ 2 * 1 * 1 : ℝ) : ℂ) + Complex.I * ((1 * 1 * 1 : ℝ) : ℂ) := by
  exact_mod_cast opposite_sign_equation_ne 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Modulus of the travelling phasor at `sigma = 1`, depth `z = 2`. -/
example : ‖Complex.exp (-propagationConstant 1 1 1 1 * (2 : ℂ))‖ =
    Real.exp (-attenuationConstant 1 1 1 1 * 2) :=
  abs_exp_neg_propagationConstant_mul 1 1 1 1 2

end PhyslibExtTest.Electromagnetism.ConductingPlaneWave

/-! ## C. Axiom audit -/

open PhyslibExt.Electromagnetism.ConductingPlaneWave

#print axioms attenuationConstant_nonneg
#print axioms phaseConstant_pos
#print axioms attenuationConstant_pos_of_sigma_pos
#print axioms propagationConstant_eq
#print axioms propagationConstant_sq
#print axioms propagationConstant_sq_eq
#print axioms dispersion_verification
#print axioms attenuationConstant_zero_sigma
#print axioms phaseConstant_zero_sigma
#print axioms propagationConstant_zero_sigma
#print axioms skinDepth_pos_and_mul_eq_one
#print axioms neg_propagationConstant_not_forward
#print axioms opposite_sign_equation_ne
#print axioms abs_exp_neg_propagationConstant_mul
#print axioms planeWave_eq_re_phasor_at_zero_sigma
#print axioms planeWave_eq_re_forward_phasor_at_zero_sigma
