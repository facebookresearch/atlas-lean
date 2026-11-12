/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.GasEquations

/-!
# Gas equations of state checks

Concrete consumers of `PhyslibExt.Chemistry.GasEquations`, mostly at the clean van der Waals
parameters `R = 1`, `a = 27`, `b = 1`, for which `V_c = 3`, `T_c = 8` and `p_c = 1`.

## i. Overview

These are elaboration, exact-value and non-vacuity checks, not new results: Dalton partial
pressures and the ideal-gas identity, the critical constants and the critical equations, the
reduced equation, the virial identity and the Boyle temperature, boundary probes showing that
the domain hypotheses matter, two compositional examples, and an axiom audit.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Dalton partial pressures and the ideal-gas model
- B. The van der Waals critical point
- C. The reduced van der Waals equation
- D. Virial coefficients and the Boyle temperature
- E. Boundary probes
- F. Compositional examples
- G. Axiom audit

## iv. References

- `PhyslibExt.Chemistry.GasEquations`
-/

open Chemistry.GasEquations

/-! ## A. Dalton partial pressures and the ideal-gas model -/

/-- Mole fractions `1/2, 1/3, 1/6` sum to `1`, so at `p = 6` the partial pressures sum to `6`. -/
example : ∑ i, partialPressure (![1 / 2, 1 / 3, 1 / 6] i) 6 = (6 : ℝ) :=
  sum_partialPressure _ 6 (by norm_num [Fin.sum_univ_three])

/-- The individual partial pressures are `3, 2, 1`. -/
example : partialPressure (1 / 2) 6 = (3 : ℝ) ∧ partialPressure (1 / 3) 6 = (2 : ℝ) ∧
    partialPressure (1 / 6) 6 = (1 : ℝ) := by
  norm_num [partialPressure]

/-- Amounts `2, 3` (so `N = 5`) at `R = 1`, `T = 300`, `V = 10`: each component pressure
`n i R T / V` equals `x_i p` with `x = 2/5, 3/5` and `p = N R T / V`. -/
example : (2 : ℝ) * 1 * 300 / 10 = partialPressure (2 / 5) (5 * 1 * 300 / 10) ∧
    (3 : ℝ) * 1 * 300 / 10 = partialPressure (3 / 5) (5 * 1 * 300 / 10) := by
  have h := idealGas_pressure_alone_eq_partialPressure ![(2 : ℝ), 3] 5 10 300 1 (by norm_num)
    (by norm_num [Fin.sum_univ_two]) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h 0, h 1⟩

/-- The numbers: `p = 150`, component pressures `60` and `90`. -/
example : (5 : ℝ) * 1 * 300 / 10 = 150 ∧ (2 : ℝ) * 1 * 300 / 10 = 60 ∧
    (3 : ℝ) * 1 * 300 / 10 = 90 ∧ partialPressure (2 / 5) 150 = (60 : ℝ) ∧
    partialPressure (3 / 5) 150 = (90 : ℝ) := by
  norm_num [partialPressure]

/-! ## B. The van der Waals critical point -/

/-- With `R = 1`, `a = 27`, `b = 1`, the critical equations force `V_c = 3`, `T_c = 8`,
`p_c = 1` and `Z_c = 3 / 8`. -/
example (T Vm : ℝ) (hT : 0 < T) (hVm : 1 < Vm)
    (h₁ : -1 * T / (Vm - 1) ^ 2 + 2 * 27 / Vm ^ 3 = 0)
    (h₂ : 2 * 1 * T / (Vm - 1) ^ 3 - 6 * 27 / Vm ^ 4 = 0) :
    Vm = 3 ∧ T = 8 ∧ vdWPressure 27 1 1 T Vm = 1 ∧
      compressibilityFactor (vdWPressure 27 1 1 T Vm) Vm 1 T = 3 / 8 := by
  obtain ⟨hV, hTc, hp, hZ⟩ :=
    vdW_critical_point 27 1 1 T Vm (by norm_num) (by norm_num) (by norm_num) hT hVm h₁ h₂
  norm_num at hV hTc hp
  exact ⟨hV, hTc, hp, hZ⟩

/-- The critical values `(V_m, T) = (3, 8)` satisfy both critical equations:
`-8 / 4 + 54 / 27 = 0` and `16 / 8 - 162 / 81 = 0`. -/
example : -(1 : ℝ) * 8 / (3 - 1) ^ 2 + 2 * 27 / 3 ^ 3 = 0 ∧
    2 * 1 * 8 / ((3 : ℝ) - 1) ^ 3 - 6 * 27 / 3 ^ 4 = 0 := by
  norm_num

/-- Equivalently, both derivatives of the van der Waals pressure vanish at `V_m = 3`, `T = 8`. -/
example : deriv (fun V => vdWPressure 27 1 1 8 V) 3 = 0 ∧
    deriv (deriv fun V => vdWPressure 27 1 1 8 V) 3 = 0 := by
  rw [(hasDerivAt_vdWPressure 27 1 1 8 3 (by norm_num) (by norm_num)).deriv,
    (hasDerivAt_deriv_vdWPressure 27 1 1 8 3 (by norm_num) (by norm_num)).deriv]
  norm_num

/-- The derivative form of the critical theorem gives the same constants. -/
example (T Vm : ℝ) (hT : 0 < T) (hVm : 1 < Vm)
    (h₁ : deriv (fun V => vdWPressure 27 1 1 T V) Vm = 0)
    (h₂ : deriv (deriv fun V => vdWPressure 27 1 1 T V) Vm = 0) : Vm = 3 ∧ T = 8 := by
  obtain ⟨hV, hTc, -, -⟩ :=
    vdW_critical_point_of_deriv 27 1 1 T Vm (by norm_num) (by norm_num) (by norm_num) hT hVm h₁ h₂
  norm_num at hV hTc
  exact ⟨hV, hTc⟩

/-! ## C. The reduced van der Waals equation -/

/-- At `V_m = 6`, `T = 16` (so `V_r = 2`, `T_r = 2`) the reduced equation forces
`P_r = 49 / 20`. -/
example (Pr : ℝ) (hPr : Pr = vdWReducedPressure 27 1 (vdWPressure 27 1 1 16 6)) :
    Pr = 49 / 20 := by
  have h := reduced_vdW_equation 27 1 1 16 6 _ Pr 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) rfl hPr (by norm_num [vdWReducedVolume])
    (by norm_num [vdWReducedTemperature])
  norm_num at h
  linarith

/-- Cross-check: `p = 16 / 5 - 27 / 36 = 49 / 20` and `p_c = 27 / 27 = 1`. -/
example : vdWReducedPressure 27 1 (vdWPressure 27 1 1 16 6) = 49 / 20 := by
  norm_num [vdWReducedPressure, vdWPressure]

/-! ## D. Virial coefficients and the Boyle temperature -/

/-- At `V_m = 4`, `T = 8`: `Z = (8 / 3 - 27 / 16) * 4 / 8 = 47 / 96` and
`B = 1 - 27 / 8 = -19 / 8`. -/
example : compressibilityFactor (vdWPressure 27 1 1 8 4) 4 1 8 = 47 / 96 ∧
    vdWSecondVirialCoeff 27 1 1 8 = -19 / 8 := by
  norm_num [compressibilityFactor, vdWPressure, vdWSecondVirialCoeff]

/-- The exact virial identity there: `47 / 96 = 1 + (-19 / 8) / 4 + 1 / (4 * 3)`. -/
example : compressibilityFactor (vdWPressure 27 1 1 8 4) 4 1 8 =
    1 + vdWSecondVirialCoeff 27 1 1 8 / 4 + 1 ^ 2 / (4 * (4 - 1)) :=
  vdW_virial_expansion 27 1 1 8 4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) rfl

/-- The Boyle temperature at the clean parameters is `a / (R b) = 27`, and `B(27) = 0`. -/
example : vdWSecondVirialCoeff 27 1 1 (27 / (1 * 1)) = 0 :=
  (vdWSecondVirialCoeff_eq_zero_iff 27 1 1 _ (by norm_num) (by norm_num) (by norm_num)).2 rfl

/-- Direct evaluation: `B(27) = 1 - 27 / 27 = 0`. -/
example : vdWSecondVirialCoeff 27 1 1 27 = 0 := by
  norm_num [vdWSecondVirialCoeff]

/-- Away from the Boyle temperature the coefficient does not vanish. -/
example : vdWSecondVirialCoeff 27 1 1 8 ≠ 0 := by
  rw [Ne, vdWSecondVirialCoeff_eq_zero_iff 27 1 1 8 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ## E. Boundary probes -/

/-- At `V_m = b` the denominator `V_m - b` vanishes and Lean's `x / 0 = 0` gives the junk value
`vdWPressure 27 1 1 8 1 = -27`. Every van der Waals result of the module (the derivative lemmas,
the critical point, the reduced equation and the virial identity) assumes `b < V_m`, which fails
here, so none of them applies at `V_m = b`; the Dalton, ideal-gas and Boyle results do not
involve `V_m`. -/
example : (1 : ℝ) - 1 = 0 ∧ vdWPressure 27 1 1 8 1 = -27 ∧ ¬ (1 : ℝ) < 1 := by
  norm_num [vdWPressure]

/-- The hypothesis `b < V_m` of `vdW_virial_expansion` cannot be dropped: at `V_m = b = 1`,
`T = 8`, the compressibility factor is `-27 / 8` while the right-hand side is `-11 / 8`. -/
example : compressibilityFactor (vdWPressure 27 1 1 8 1) 1 1 8 ≠
    1 + vdWSecondVirialCoeff 27 1 1 8 / 1 + 1 ^ 2 / (1 * (1 - 1)) := by
  norm_num [compressibilityFactor, vdWPressure, vdWSecondVirialCoeff]

/-- `(V_m, T) = (4, 8)` is not critical: `∂p/∂V_m = -8 / 9 + 54 / 64 = -13 / 288 ≠ 0`. -/
example : -(1 : ℝ) * 8 / (4 - 1) ^ 2 + 2 * 27 / 4 ^ 3 ≠ 0 := by
  norm_num

/-- The same failure, stated with the derivative itself. -/
example : deriv (fun V => vdWPressure 27 1 1 8 V) 4 ≠ 0 := by
  rw [(hasDerivAt_vdWPressure 27 1 1 8 4 (by norm_num) (by norm_num)).deriv]
  norm_num

/-- The critical theorem rules out `(4, 8)` too, since `4 ≠ 3 b`. -/
example : ¬ (-(1 : ℝ) * 8 / (4 - 1) ^ 2 + 2 * 27 / 4 ^ 3 = 0 ∧
    2 * 1 * 8 / ((4 : ℝ) - 1) ^ 3 - 6 * 27 / 4 ^ 4 = 0) := by
  rintro ⟨h₁, h₂⟩
  have h := (vdW_critical_point 27 1 1 8 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h₁ h₂).1
  norm_num at h

/-- The Boyle equivalence needs `0 < a`: for `a = 0` and `T = 0 = a / (R b)`,
`B(0) = b = 1 ≠ 0`. -/
example : ¬ (vdWSecondVirialCoeff 0 1 1 0 = 0 ↔ (0 : ℝ) = 0 / (1 * 1)) := by
  norm_num [vdWSecondVirialCoeff]

/-! ## F. Compositional examples -/

/-- From the critical equations to the reduced variables: the critical theorem gives
`P_r = V_r = T_r = 1` at the critical point, and the reduced theorem gives the reduced equation
there, `(1 + 3 / 1 ^ 2) (3 * 1 - 1) = 8 * 1`. -/
example (T Vm : ℝ) (hT : 0 < T) (hVm : 1 < Vm)
    (h₁ : -1 * T / (Vm - 1) ^ 2 + 2 * 27 / Vm ^ 3 = 0)
    (h₂ : 2 * 1 * T / (Vm - 1) ^ 3 - 6 * 27 / Vm ^ 4 = 0) :
    vdWReducedPressure 27 1 (vdWPressure 27 1 1 T Vm) = 1 ∧ vdWReducedVolume 1 Vm = 1 ∧
      vdWReducedTemperature 27 1 1 T = 1 ∧
      (vdWReducedPressure 27 1 (vdWPressure 27 1 1 T Vm) + 3 / vdWReducedVolume 1 Vm ^ 2) *
        (3 * vdWReducedVolume 1 Vm - 1) = 8 * vdWReducedTemperature 27 1 1 T := by
  obtain ⟨hV, hTc, hp, -⟩ :=
    vdW_critical_point 27 1 1 T Vm (by norm_num) (by norm_num) (by norm_num) hT hVm h₁ h₂
  refine ⟨?_, ?_, ?_, reduced_vdW_equation 27 1 1 T Vm _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) hT hVm rfl rfl rfl rfl⟩
  · rw [hp]
    norm_num [vdWReducedPressure]
  · rw [hV]
    norm_num [vdWReducedVolume]
  · rw [hTc]
    norm_num [vdWReducedTemperature]

/-- Dalton with the ideal-gas identity: the alone-pressures `60` and `90` of the two-species
ideal mixture above add up to the total pressure `150`. -/
example : ∑ i, ![(2 : ℝ), 3] i * 1 * 300 / 10 = 5 * 1 * 300 / 10 := by
  have h := idealGas_pressure_alone_eq_partialPressure ![(2 : ℝ), 3] 5 10 300 1 (by norm_num)
    (by norm_num [Fin.sum_univ_two]) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [h]
  exact sum_partialPressure _ _ (by norm_num [Fin.sum_univ_two])

/-! ## G. Axiom audit -/

#print axioms Chemistry.GasEquations.partialPressure
#print axioms Chemistry.GasEquations.sum_partialPressure
#print axioms Chemistry.GasEquations.idealGas_pressure_alone_eq_partialPressure
#print axioms Chemistry.GasEquations.vdWPressure
#print axioms Chemistry.GasEquations.hasDerivAt_vdWPressure
#print axioms Chemistry.GasEquations.hasDerivAt_deriv_vdWPressure
#print axioms Chemistry.GasEquations.compressibilityFactor
#print axioms Chemistry.GasEquations.vdW_critical_point
#print axioms Chemistry.GasEquations.vdW_critical_point_of_deriv
#print axioms Chemistry.GasEquations.vdWReducedPressure
#print axioms Chemistry.GasEquations.vdWReducedVolume
#print axioms Chemistry.GasEquations.vdWReducedTemperature
#print axioms Chemistry.GasEquations.reduced_vdW_equation
#print axioms Chemistry.GasEquations.vdWSecondVirialCoeff
#print axioms Chemistry.GasEquations.vdW_virial_expansion
#print axioms Chemistry.GasEquations.vdWSecondVirialCoeff_eq_zero_iff
