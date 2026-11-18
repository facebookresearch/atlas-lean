/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BoxTerminalFlux

@[expose] public section

open PhyslibExt.Circuits.BoxTerminalFlux

namespace PhyslibExtTest.Circuits.BoxTerminalFlux

/-- Through-flow currents `(-3, 3, 0, 0, 0, 0)` sum to zero. -/
example : ∑ f : Fin 6, (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f = 0 :=
  throughFlow_currents_sum_example

/-- Accumulating-charge currents sum to `-2`, keeping the nonzero
charge-rate term. -/
example : ∑ f : Fin 6, (![-2, 0, 0, 0, 0, 0] : Fin 6 → ℝ) f = -2 :=
  accumulatingCharge_currents_sum_example

/-- Omitting the entering face leaves a nonzero sum. -/
example : ∑ f : Fin 6, (![0, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f ≠ 0 :=
  omittedFace_currents_sum_example

/-- The ohmic density at a point is conductivity times the normal
field component: `2 * 3 = 6`. -/
example : ohmicDensity 2 (fun _ _ => 3) 0 (0, 0) = 6 := by
  norm_num [ohmicDensity, PhyslibExt.Circuits.UniformOhmicBar.ohmCurrentDensity]

/-- With zero charge rate, the end-face currents of the through-flow
example cancel. -/
example : (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) 0 +
    (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) 1 = 0 := by
  have hsum : ∑ f : Fin 6, (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) f = -(0 : ℝ) := by
    rw [neg_zero]
    exact throughFlow_currents_sum_example
  have h := endFaceCurrents_add_eq_neg_chargeRate_of_sideFaces_zero
    (![-3, 3, 0, 0, 0, 0] : Fin 6 → ℝ) 0 hsum (by
      intro f hf0 hf1
      fin_cases f <;> simp_all)
  rw [neg_zero] at h
  exact h

end PhyslibExtTest.Circuits.BoxTerminalFlux
