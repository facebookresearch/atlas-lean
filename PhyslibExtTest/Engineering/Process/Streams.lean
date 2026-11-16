/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.Streams

/-!
# Tests for process stream composition

Boundary checks for `PhyslibExt.Engineering.Process.Streams`: flows `(1, 2)`
with molar masses `(2, 3)` integrated over duration `4` give amounts `(4, 8)`,
mole fractions `(1/3, 2/3)` and mass fractions `(1/4, 3/4)`; a zero component
is allowed; a zero duration does not retain the fractions.
-/

namespace Engineering.Process.Streams.Tests

open StreamFlow

/-- Two-species stream with flows `(1, 2)` mol per time unit. -/
def s12 : StreamFlow (Fin 2) :=
  ⟨![1, 2], by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]⟩

/-- Two-species stream with a zero component, flows `(0, 2)`. -/
def s02 : StreamFlow (Fin 2) :=
  ⟨![0, 2], by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]⟩

/-- Molar masses `(2, 3)` for the two species. -/
def M23 : Fin 2 → ℝ := ![2, 3]

example : s12.total = 3 := by
  simp only [s12, StreamFlow.total, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

example : Chemistry.Amounts.moleFraction s12.flow 0 = 1 / 3 := by
  simp only [Chemistry.Amounts.moleFraction, s12, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

example : Chemistry.Amounts.moleFraction s12.flow 1 = 2 / 3 := by
  simp only [Chemistry.Amounts.moleFraction, s12, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

-- A zero component is allowed in a positive-total stream.
example : Chemistry.Amounts.moleFraction s02.flow 0 = 0 := by
  simp only [Chemistry.Amounts.moleFraction, s02, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

example : Chemistry.Amounts.moleFraction s02.flow 1 = 1 := by
  simp only [Chemistry.Amounts.moleFraction, s02, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

-- Integrating flows (1, 2) over duration 4 gives amounts (4, 8).
example : s12.integrate 4 0 = 4 ∧ s12.integrate 4 1 = 8 := by
  constructor
  · simp only [StreamFlow.integrate, s12]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · simp only [StreamFlow.integrate, s12]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

-- The integrated batch retains fractions (1/3, 2/3).
example : Chemistry.Amounts.moleFraction (s12.integrate 4) 0 = 1 / 3 := by
  simp only [Chemistry.Amounts.moleFraction, StreamFlow.integrate, s12, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

example : Chemistry.Amounts.moleFraction (s12.integrate 4) 1 = 2 / 3 := by
  simp only [Chemistry.Amounts.moleFraction, StreamFlow.integrate, s12, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

-- Mass fractions for molar masses (2, 3) are (1/4, 3/4).
example : Chemistry.Amounts.massFraction M23 s12.flow 0 = 1 / 4 := by
  simp only [Chemistry.Amounts.massFraction, M23, s12, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

example : Chemistry.Amounts.massFraction M23 s12.flow 1 = 3 / 4 := by
  simp only [Chemistry.Amounts.massFraction, M23, s12, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

-- Assumption necessity: zero duration does not retain the fractions.
example : Chemistry.Amounts.moleFraction (s12.integrate 0) 0 = 0 := by
  have h : s12.integrate 0 = fun _ => 0 := StreamFlow.integrate_zero s12
  rw [h]
  simp [Chemistry.Amounts.moleFraction, Finset.sum_const_zero]

example :
    Chemistry.Amounts.moleFraction (s12.integrate 0) ≠
      Chemistry.Amounts.moleFraction s12.flow := by
  have e1 : Chemistry.Amounts.moleFraction (s12.integrate 0) 0 = 0 := by
    have h : s12.integrate 0 = fun _ => 0 := StreamFlow.integrate_zero s12
    rw [h]
    simp [Chemistry.Amounts.moleFraction, Finset.sum_const_zero]
  have e2 : Chemistry.Amounts.moleFraction s12.flow 0 = 1 / 3 := by
    simp only [Chemistry.Amounts.moleFraction, s12, Fin.sum_univ_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  intro h
  have h0 := congrFun h 0
  rw [e1, e2] at h0
  norm_num at h0

end Engineering.Process.Streams.Tests
