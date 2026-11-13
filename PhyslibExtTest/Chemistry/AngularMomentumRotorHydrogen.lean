/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.AngularMomentumRotorHydrogen

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Angular momentum, rigid rotor and hydrogen-like atom checks

Concrete consumers of `PhyslibExt.Chemistry.AngularMomentumRotorHydrogen`, plus
`#print axioms` diagnostics for its results.

## i. Overview

These are elaboration and non-vacuity checks, not new results: concrete commutator, Casimir
and `Lz` values; the irreducibility theorems applied to an invariant subspace that contains a
basis vector; rotor and hydrogen values; the principal-quantum-number domain `ℕ+` of the
hydrogen levels, degeneracies and Rydberg lines; the bridge to Physlib's Bohr levels; and the
shell and orbital counts.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Angular momentum
- B. Rigid rotor and hydrogen-like atom
- C. Shell capacity and Hund's rule
- D. Axiom diagnostics

## iv. References

- `PhyslibExt.Chemistry.AngularMomentumRotorHydrogen`
-/

@[expose] public section

namespace PhyslibExtTest.Chemistry.AngularMomentumRotorHydrogen

open scoped BigOperators
open scoped Matrix
open PhyslibExt.Chemistry.AngularMomentumRotorHydrogen

/-! ## A. Angular momentum -/

/-- Concrete spin-1/2 commutator entry at `hbar = 1`. -/
theorem test_spinHalf_commutator_entry :
    ⁅spinHalfJx 1, spinHalfJy 1⁆ 0 0 = Complex.I / 2 := by
  rw [(spinHalf_commutators 1).1]
  simp [spinHalfJz, PauliMatrix.pauliMatrix]
  ring

/-- Concrete spin-1/2 Casimir entry at `hbar = 1`. -/
theorem test_spinHalf_casimir_entry :
    (spinHalfJx 1 ^ 2 + spinHalfJy 1 ^ 2 + spinHalfJz 1 ^ 2) 0 0 = 3 / 4 := by
  rw [spinHalf_casimir 1]
  simp

/-- The `l = 0` commutator and Casimir at `hbar = 1`. -/
theorem test_lZero :
    ⁅lZeroL, lZeroL⁆ = (Complex.I * ((1 : ℝ) : ℂ)) • lZeroL ∧
      lZeroL ^ 2 + lZeroL ^ 2 + lZeroL ^ 2 = 0 :=
  ⟨lZero_commutator 1, lZero_casimir⟩

/-- Concrete l = 1 `Lz` eigenvector. -/
theorem test_lOneLz_vector :
    lOneLz 1 *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h01 : ![1, 0, 0] = Pi.single 0 (1 : ℂ) := by
    ext k
    fin_cases k <;> simp [Pi.single_eq_of_ne, h10, h20]
  rw [h01, (l1_Lz_eigenvalues 1).1]
  simp

/-- `l = 0` irreducibility: a subspace of `Fin 1 → ℂ` containing the basis vector is `⊤`. -/
theorem test_lZero_irreducible_top (W : Submodule ℂ (Fin 1 → ℂ))
    (h0 : Pi.single 0 (1 : ℂ) ∈ W) : W = ⊤ := by
  rcases lZero_irreducible W with h | h
  · rw [h, Submodule.mem_bot] at h0
    simpa using congrFun h0 0
  · exact h

/-- Spin-1/2 irreducibility at `hbar = 1`: a subspace invariant under `Jx` and `Jz` that
contains `e₀` is `⊤`. -/
theorem test_spinHalf_irreducible_top (W : Submodule ℂ (Fin 2 → ℂ))
    (hx : ∀ v ∈ W, spinHalfJx 1 *ᵥ v ∈ W) (hz : ∀ v ∈ W, spinHalfJz 1 *ᵥ v ∈ W)
    (h0 : Pi.single 0 (1 : ℂ) ∈ W) : W = ⊤ := by
  rcases spinHalf_irreducible one_ne_zero W hx hz with h | h
  · rw [h, Submodule.mem_bot] at h0
    simpa using congrFun h0 0
  · exact h

/-- `l = 1` irreducibility at `hbar = 1`: a subspace invariant under `Lx` and `Lz` that
contains the `m = 0` basis vector is `⊤`. -/
theorem test_lOne_irreducible_top (W : Submodule ℂ (Fin 3 → ℂ))
    (hx : ∀ v ∈ W, lOneLx 1 *ᵥ v ∈ W) (hz : ∀ v ∈ W, lOneLz 1 *ᵥ v ∈ W)
    (h1 : Pi.single 1 (1 : ℂ) ∈ W) : W = ⊤ := by
  rcases lOne_irreducible one_ne_zero W hx hz with h | h
  · rw [h, Submodule.mem_bot] at h1
    simpa using congrFun h1 1
  · exact h

/-- The carrier dimensions `1, 2, 3`. -/
theorem test_rep_dimension_three : Module.finrank ℂ (Fin 3 → ℂ) = 3 :=
  angularMomentum_rep_dimensions.2.2

/-! ## B. Rigid rotor and hydrogen-like atom -/

/-- Concrete rigid-rotor energies. -/
theorem test_rigidRotorEnergy_values :
    rigidRotorEnergy 1 1 0 = 0 ∧ rigidRotorEnergy 1 1 1 = 1 ∧
      rigidRotorEnergy 1 1 2 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [rigidRotorEnergy]

/-- Concrete magnetic count at `J = 2`. -/
theorem test_rigidRotorMagnetic_two : (Finset.Icc (-(2 : ℤ)) (2 : ℤ)).card = 5 := by
  exact_mod_cast rigidRotorMagnetic_count 2

/-- Concrete hydrogen energies. -/
theorem test_hydrogenEnergy_values :
    hydrogenEnergy 1 1 1 = -1 ∧ hydrogenEnergy 1 1 2 = -1 / 4 := by
  refine ⟨?_, ?_⟩ <;> norm_num [hydrogenEnergy]

/-- Domain: the levels are indexed by the principal quantum number `n : ℕ+`, so every level is
bound. For `Z ≠ 0` and `R > 0`, `hydrogenEnergy Z R n < 0` for every `n`; there is no junk
level `n = 0` with energy `0`. -/
theorem test_hydrogenEnergy_neg {Z R : ℝ} (hZ : Z ≠ 0) (hR : 0 < R) (n : ℕ+) :
    hydrogenEnergy Z R n < 0 := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hZR : 0 < Z ^ 2 * R := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hZR) (by positivity)

/-- Domain: the ground state is `n = 1`, with energy `-Z^2 R`. -/
theorem test_hydrogenEnergy_ground (Z R : ℝ) : hydrogenEnergy Z R 1 = -(Z ^ 2 * R) := by
  simp [hydrogenEnergy]

/-- Concrete hydrogen degeneracy: the ground level `n = 1` has one orbital state. -/
theorem test_hydrogen_degeneracy_ground :
    ∑ l ∈ Finset.range ((1 : ℕ+) : ℕ), (2 * l + 1) = 1 := by
  rw [hydrogen_degeneracy]
  rfl

/-- Concrete hydrogen degeneracy at `n = 2`. -/
theorem test_hydrogen_degeneracy_two :
    ∑ l ∈ Finset.range ((2 : ℕ+) : ℕ), (2 * l + 1) = 4 := by
  rw [hydrogen_degeneracy]
  rfl

/-- The 2s radial node at `r = 2`. -/
theorem test_hydrogenRadial20_node : hydrogenRadial20 2 = 0 := by
  norm_num [hydrogenRadial20]

/-- 2p vanishes at the origin. -/
theorem test_hydrogenRadial21_origin : hydrogenRadial21 0 = 0 := by
  norm_num [hydrogenRadial21]

/-- Concrete Rydberg line. -/
theorem test_rydberg_line : rydbergWavenumber 1 1 1 2 = 3 / 4 := by
  norm_num [rydbergWavenumber]

/-- Domain: the Lyman-alpha line `2 → 1` is positive, with no separate positivity hypothesis
on the lower principal quantum number. -/
theorem test_rydberg_lyman_alpha_pos : 0 < rydbergWavenumber 1 1 1 2 :=
  rydbergWavenumber_pos one_pos one_ne_zero (by decide)

/-- Bridge: Physlib's ground level `0` of a three-dimensional hydrogen atom is the level with
principal quantum number `1`. -/
theorem test_energyLevel_ground (H : QuantumMechanics.HydrogenAtom) (hd : H.d = 3) :
    H.energyLevel 0 = hydrogenEnergy 1 H.rydbergEnergy 1 :=
  energyLevel_eq_hydrogenEnergy H hd 0

/-! ## C. Shell capacity and Hund's rule -/

/-- Concrete capacity of the principal shells `n ≤ 2`: `2 + 8 = 10` electrons. -/
theorem test_principalShells_capacity_two :
    ∑ n ∈ Finset.Icc (1 : ℕ) 2, 2 * ((n : ℝ)) ^ 2 = 10 := by
  rw [principalShells_capacity]
  norm_num

/-- Concrete Hund count. -/
theorem test_hundUnpaired_three_three : hundUnpaired 3 3 = 3 := by
  decide

/-! ## D. Axiom diagnostics -/

#print axioms lZero_commutator
#print axioms lZero_casimir
#print axioms spinHalf_commutators
#print axioms spinHalf_casimir
#print axioms lOne_commutators
#print axioms lOne_casimir
#print axioms lZero_irreducible
#print axioms spinHalf_irreducible
#print axioms lOne_irreducible
#print axioms angularMomentum_rep_dimensions
#print axioms rigidRotorEnergy_spacing
#print axioms rigidRotorMagnetic_count
#print axioms l1_Lz_eigenvalues
#print axioms sphericalHarmonic10_at_pole
#print axioms rigidRotorEnergy_l1
#print axioms hydrogenEnergy_scaling
#print axioms sum_range_odd_eq_sq
#print axioms hydrogen_degeneracy
#print axioms hydrogen_degeneracy_spin
#print axioms radialResidual_1s
#print axioms radialResidual_2s
#print axioms radialResidual_2p
#print axioms hydrogenRadial_deriv_1s
#print axioms hydrogenRadial_deriv_2s
#print axioms hydrogenRadial_deriv_2p
#print axioms rydbergWavenumber_pos
#print axioms energyLevel_eq_hydrogenEnergy
#print axioms wavelength_inv_eq_rydbergWavenumber
#print axioms principalShells_capacity
#print axioms hundUnpaired_le_g

end PhyslibExtTest.Chemistry.AngularMomentumRotorHydrogen
