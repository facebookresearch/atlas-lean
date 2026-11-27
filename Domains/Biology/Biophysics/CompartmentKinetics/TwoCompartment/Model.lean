/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Two-compartment model generator

The two-compartment amount equations in matrix form, their
component equations, the augmented sink budget, and the
zero-exchange reduction.
-/

@[expose] public section

open Matrix Finset

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model

/-- The two-compartment generator for rates `k10, k12, k21`. -/
def pk2Generator (k10 k12 k21 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-(k10 + k12), k21], ![k12, -k21]]

/-- **Central component equation.** The first component of the
generator action is `-(k10 + k12) * A1 + k21 * A2`. -/
theorem pk2_central_component (k10 k12 k21 A1 A2 : ℝ) :
    (pk2Generator k10 k12 k21 *ᵥ ![A1, A2]) 0 =
      -(k10 + k12) * A1 + k21 * A2 := by
  simp [pk2Generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Peripheral component equation.** The second component is
`k12 * A1 - k21 * A2`. -/
theorem pk2_peripheral_component (k10 k12 k21 A1 A2 : ℝ) :
    (pk2Generator k10 k12 k21 *ᵥ ![A1, A2]) 1 =
      k12 * A1 - k21 * A2 := by
  simp [pk2Generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The augmented three-state generator with the eliminated
sink as a third state, acting on `[A₁, A₂, sink]`. -/
def pk2AugmentedGenerator (k10 k12 k21 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![-(k10 + k12), k21, 0], ![k12, -k21, 0], ![k10, 0, 0]]

/-- **Augmented column budget.** Every column of the augmented
generator sums to zero: adjoining the sink makes the amount
dynamics conservative. -/
theorem pk2_augmented_budget (k10 k12 k21 : ℝ) (j : Fin 3) :
    ∑ i, pk2AugmentedGenerator k10 k12 k21 i j = 0 := by
  fin_cases j <;> simp [pk2AugmentedGenerator, Fin.sum_univ_three] <;> ring

/-- **Zero-exchange reduction.** With `k12 = 0` and no
peripheral amount, the central equation is pure elimination. -/
theorem pk2_zero_exchange (k10 k21 A1 : ℝ) :
    (pk2Generator k10 0 k21 *ᵥ ![A1, 0]) 0 = -k10 * A1 := by
  simp [pk2Generator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartment.Model
