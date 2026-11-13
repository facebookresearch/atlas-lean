/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.AngularMomentumRotorHydrogen
public import Mathlib.Tactic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Interval.Finset.Basic

@[expose] public section

/-!
# Tests for CH38: angular momentum, rigid rotor and hydrogen-like atom

Concrete evaluations of the production theorems plus `#print axioms` checks.
-/

namespace PhyslibExtTest.Chemistry.AngularMomentumRotorHydrogen

open scoped BigOperators
open scoped Matrix
open PhyslibExt.Chemistry.AngularMomentumRotorHydrogen

/-- Concrete spin-1/2 commutator entry at `hbar = 1`. -/
theorem test_spinHalf_commutator_entry :
    (commutator (spinHalfJx 1) (spinHalfJy 1)) 0 0 = Complex.I / 2 := by
  have hcomm := (spinHalf_commutators 1).1
  rw [hcomm] <;>
    simp [Matrix.smul_apply, spinHalfJz, pauliZ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.ofReal_one] <;>
    ring

/-- Concrete spin-1/2 Casimir entry at `hbar = 1`. -/
theorem test_spinHalf_casimir_entry :
    (spinHalfJx 1 ^ 2 + spinHalfJy 1 ^ 2 + spinHalfJz 1 ^ 2) 0 0 = 3 / 4 := by
  rw [spinHalf_casimir 1] <;>
    simp [Matrix.smul_apply, Matrix.one_apply, Complex.ofReal_one] <;>
    ring

/-- Concrete l = 1 `Lz` eigenvector. -/
theorem test_lOneLz_vector :
    lOneLz 1 *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h01 : ![1, 0, 0] = Pi.single 0 (1 : ℂ) := by
    ext k
    fin_cases k <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_eq_same,
        Pi.single_eq_of_ne, h10, h20]
  rw [h01, (l1_Lz_eigenvalues 1).1] <;> simp

/-- Concrete rigid-rotor energies. -/
theorem test_rigidRotorEnergy_values :
    rigidRotorEnergy 1 1 0 = 0 ∧ rigidRotorEnergy 1 1 1 = 1 ∧
      rigidRotorEnergy 1 1 2 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold rigidRotorEnergy <;> norm_num

/-- Concrete magnetic count at `J = 2`. -/
theorem test_rigidRotorMagnetic_two : (Finset.Icc (-(2 : ℤ)) (2 : ℤ)).card = 5 := by
  have h := rigidRotorMagnetic_count 2
  simpa using h

/-- Concrete hydrogen energies. -/
theorem test_hydrogenEnergy_values :
    hydrogenEnergy 1 1 1 = -1 ∧ hydrogenEnergy 1 1 2 = -1 / 4 := by
  refine ⟨?_, ?_⟩ <;> unfold hydrogenEnergy <;> norm_num

/-- Concrete hydrogen degeneracy at `n = 2`. -/
theorem test_hydrogen_degeneracy_two :
    ∑ l ∈ Finset.range 2, (2 * l + 1) = 4 := by
  simp [hydrogen_degeneracy]

/-- The 2s radial node at `r = 2`. -/
theorem test_hydrogenRadial20_node : hydrogenRadial20 2 = 0 := by
  unfold hydrogenRadial20
  norm_num

/-- 2p vanishes at the origin. -/
theorem test_hydrogenRadial21_origin : hydrogenRadial21 0 = 0 := by
  unfold hydrogenRadial21
  norm_num

/-- Concrete Rydberg line. -/
theorem test_rydberg_line : rydbergWavenumber 1 1 1 2 = 3 / 4 := by
  unfold rydbergWavenumber <;> norm_num

/-- Concrete Aufbau capacity at `N = 2`. -/
theorem test_aufbau_two : ∑ n ∈ Finset.Icc (1 : ℕ) 2, 2 * ((n : ℝ)) ^ 2 = 10 := by
  rw [aufbau_shellCapacity] <;> norm_num

/-- Concrete Hund count. -/
theorem test_hundUnpaired_three_three : hundUnpaired 3 3 = 3 := by
  decide

#print axioms spinHalf_commutators
#print axioms spinHalf_casimir
#print axioms lOne_commutators
#print axioms lOne_casimir
#print axioms angularMomentum_rep_dimensions
#print axioms rigidRotorEnergy_spacing
#print axioms rigidRotorMagnetic_count
#print axioms l1_Lz_eigenvalues
#print axioms sphericalHarmonic10_at_pole
#print axioms rigidRotorEnergy_l1
#print axioms hydrogenEnergy_scaling
#print axioms hydrogen_degeneracy
#print axioms hydrogen_degeneracy_spin
#print axioms radialResidual_1s
#print axioms radialResidual_2s
#print axioms radialResidual_2p
#print axioms hydrogenRadial_deriv_1s
#print axioms hydrogenRadial_deriv_2s
#print axioms hydrogenRadial_deriv_2p
#print axioms rydbergWavenumber_pos
#print axioms aufbau_shellCapacity
#print axioms hundUnpaired_le_g

end PhyslibExtTest.Chemistry.AngularMomentumRotorHydrogen
