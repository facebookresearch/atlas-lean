/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.VentilationBalance
import PhyslibExt.EarthScience.Reactors
import PhyslibExt.Chemistry.SolutionComposition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Well-mixed ventilation balance checks

Concrete consumers of `PhyslibExt.Engineering.VentilationBalance`
at `V = Q = 5`, `c_out = 2`, `G = 10` (equilibrium `4`): initial
concentrations below, at, and above equilibrium, the zero-source
case and its CSTR steady form, and the ppm-versus-mass
concentration distinction.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Focused equilibrium cases
- B. Zero source, CSTR form, and ppm

## iv. References

- `PhyslibExt.Engineering.VentilationBalance`
- `PhyslibExt.EarthScience.Reactors`
- `PhyslibExt.Chemistry.SolutionComposition`
-/

open Real Filter Topology
open MathlibExt.Biology.Biophysics.CompartmentKinetics
open Engineering.VentilationBalance
open Chemistry.SolutionComposition

namespace PhyslibExtTest.Engineering.VentilationBalance

/-! ## A. Focused equilibrium cases -/

/-- The focused equilibrium is `2 + 10 / 5 = 4`. -/
example : ventilationEquilibrium 5 2 10 = 4 := by
  norm_num [ventilationEquilibrium]

/-- The compartment steady amount at the mapped parameters is
the same equilibrium. -/
example : steadyAmount (5 / 5) ((5 * 2 + 10) / 5) = 4 := by
  rw [steadyAmount_eq_ventilationEquilibrium (by norm_num) (by norm_num)]
  norm_num [ventilationEquilibrium]

/-- Below equilibrium: stays below, and is in fact strict. -/
example : ventilationConcentration 5 5 2 10 1 3 ≤ 4 := by
  have h := ventilationConcentration_le_equilibrium (by norm_num)
    (by norm_num) (V := 5) (Q := 5) (c_out := 2) (G := 10) (c0 := 1)
    (by norm_num [ventilationEquilibrium]) 3
  rwa [show ventilationEquilibrium 5 2 10 = 4 by
    norm_num [ventilationEquilibrium]] at h

example : ventilationConcentration 5 5 2 10 1 3 < 4 := by
  rw [ventilationConcentration_eq_explicit (by norm_num) (by norm_num),
    show ventilationEquilibrium 5 2 10 = 4 by
      norm_num [ventilationEquilibrium],
    show (5 : ℝ) / 5 = 1 by norm_num]
  have he : (0 : ℝ) < Real.exp (-1 * 3) := Real.exp_pos _
  have hneg : (1 - 4 : ℝ) * Real.exp (-1 * 3) < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) he
  linarith

/-- Wrong-direction control for the below-equilibrium case. -/
example : ¬ (4 : ℝ) ≤ ventilationConcentration 5 5 2 10 1 3 :=
  not_le.mpr (by
    rw [ventilationConcentration_eq_explicit (by norm_num) (by norm_num),
      show ventilationEquilibrium 5 2 10 = 4 by
        norm_num [ventilationEquilibrium],
      show (5 : ℝ) / 5 = 1 by norm_num]
    have he : (0 : ℝ) < Real.exp (-1 * 3) := Real.exp_pos _
    have hneg : (1 - 4 : ℝ) * Real.exp (-1 * 3) < 0 :=
      mul_neg_of_neg_of_pos (by norm_num) he
    linarith)

/-- Above equilibrium: stays above, and is in fact strict. -/
example : (4 : ℝ) ≤ ventilationConcentration 5 5 2 10 7 3 := by
  have h := ventilationConcentration_ge_equilibrium (by norm_num)
    (by norm_num) (V := 5) (Q := 5) (c_out := 2) (G := 10) (c0 := 7)
    (by norm_num [ventilationEquilibrium]) 3
  rwa [show ventilationEquilibrium 5 2 10 = 4 by
    norm_num [ventilationEquilibrium]] at h

example : (4 : ℝ) < ventilationConcentration 5 5 2 10 7 3 := by
  rw [ventilationConcentration_eq_explicit (by norm_num) (by norm_num),
    show ventilationEquilibrium 5 2 10 = 4 by
      norm_num [ventilationEquilibrium],
    show (5 : ℝ) / 5 = 1 by norm_num]
  have he : (0 : ℝ) < Real.exp (-1 * 3) := Real.exp_pos _
  have hpos : (0 : ℝ) < (7 - 4 : ℝ) * Real.exp (-1 * 3) :=
    mul_pos (by norm_num) he
  linarith

/-- At equilibrium: constant. -/
example : ventilationConcentration 5 5 2 10
    (ventilationEquilibrium 5 2 10) 3 = 4 := by
  rw [ventilationConcentration_at_equilibrium (by norm_num) (by norm_num)]
  norm_num [ventilationEquilibrium]

/-- Initial value and nonnegativity at the focused data. -/
example : ventilationConcentration 5 5 2 10 1 0 = 1 :=
  ventilationConcentration_zero 5 5 2 10 1

example : 0 ≤ ventilationConcentration 5 5 2 10 1 3 :=
  ventilationConcentration_nonneg (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## B. Zero source, CSTR form, and ppm -/

/-- No indoor source: the equilibrium is the outdoor
concentration, in the CSTR steady form `Q * c_out / (Q + 0 * V)`. -/
example : ventilationEquilibrium 5 2 0 = 2 :=
  ventilationEquilibrium_zero_source (by norm_num) 2

example : (5 : ℝ) * 2 / (5 + 0 * 5) = ventilationEquilibrium 5 2 0 := by
  rw [ventilationEquilibrium_zero_source (show (0:ℝ) < 5 by norm_num)]
  norm_num

/-- The CSTR steady-state identity at zero reaction rate is the
same equilibrium statement. -/
example : (5 / 5 : ℝ) * (2 - 5 * 2 / (5 + 0 * 5))
    - 0 * (5 * 2 / (5 + 0 * 5)) = 0 :=
  EarthScience.cstr_steady_state 5 5 0 2 (by norm_num) (by norm_num)
    (by norm_num)

/-- Zero source explicit profile around the outdoor value. -/
example : ventilationConcentration 5 5 2 0 1 3
    = 2 + (1 - 2) * Real.exp (-(5 / 5) * 3) := by
  rw [ventilationConcentration_eq_explicit (by norm_num) (by norm_num),
    ventilationEquilibrium_zero_source (show (0:ℝ) < 5 by norm_num)]

/-- A ppm figure is not a mass concentration: `1000` ppm by
volume of a gas of density `17988 / 10000` (kg/m³) is
`17988 / 10000000` kg/m³, not `1000`. -/
example : ppmByVolume (1 / 1000) 1 = 1000 := by
  norm_num [ppmByVolume]

example : ppmByVolume (1 / 1000) 1 / 10 ^ 6 * (17988 / 10000 : ℝ)
    = 17988 / 10000000 := by
  norm_num [ppmByVolume]

example : ¬ ((1000 : ℝ) = 17988 / 10000000) := by norm_num

#print axioms Engineering.VentilationBalance.steadyAmount_eq_ventilationEquilibrium
#print axioms Engineering.VentilationBalance.ventilationConcentration_eq_explicit
#print axioms Engineering.VentilationBalance.ventilationConcentration_hasDerivAt
#print axioms Engineering.VentilationBalance.ventilationConcentration_zero
#print axioms Engineering.VentilationBalance.ventilationConcentration_at_equilibrium
#print axioms Engineering.VentilationBalance.ventilationConcentration_le_equilibrium
#print axioms Engineering.VentilationBalance.ventilationConcentration_ge_equilibrium
#print axioms Engineering.VentilationBalance.ventilationConcentration_nonneg
#print axioms Engineering.VentilationBalance.ventilationConcentration_tendsto_equilibrium

end PhyslibExtTest.Engineering.VentilationBalance
