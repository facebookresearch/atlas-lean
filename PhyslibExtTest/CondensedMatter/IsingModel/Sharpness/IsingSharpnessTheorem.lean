/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingSharpnessTheorem

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingSharpnessUnconditional`

`ising_sharp_phase_transition` on `ℤ²`, with both regimes shown to be nonempty:
* `0 < β_c(2)` (`betaC_two_pos`, from `tildeBetaCIsing_pos` and the identification
  `β_c = β̃_c` used in the proof), so the high-temperature clauses apply at `β = 0` and at
  `β = β_c / 2`: the plus-state two-point function is summable and decays exponentially;
* the mean-field lower bound at `β = 2β_c` gives `m*(2β_c) ≥ √3 / 2 > 0`, and at `β = β_c` the
  bound reads `0 ≤ m*(β_c)`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.IsingSharpnessUnconditional

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Sharpness _root_.StatMech.Lattice

/-- The critical inverse temperature of the Ising model on `ℤ²` is positive. -/
lemma betaC_two_pos : 0 < Ising.betaC 2 := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 2) le_rfl
  have hcrit := tildeBetaCIsing_pos (d := 2) le_rfl
  have hsqrt : ∀ beta, tildeBetaCIsing 2 ≤ beta →
      Real.sqrt (1 - (tildeBetaCIsing 2 / beta) ^ 2) ≤ magnetization 2 beta :=
    fun beta hbeta => sct_magnetization_meanfield_lower_bound_integrated 2 hbdd hcrit hbeta
  rw [bc_eq_ising_of_sqrt_and_susceptibility (d := 2) (by omega) hsqrt]
  exact hcrit

-- High temperature, `β = 0`: the two-point function is summable and decays exponentially.
example : Summable (plusCorr 2 0 (Percolation.origin 2)) ∧
    ∃ c > 0, ∀ z, plusCorr 2 0 (Percolation.origin 2) z ≤
      Real.exp (-c * (l1dist 2 (Percolation.origin 2) z : ℝ)) :=
  ⟨(ising_sharp_phase_transition le_rfl).2.1 0 le_rfl betaC_two_pos,
    (ising_sharp_phase_transition le_rfl).2.2 0 le_rfl betaC_two_pos⟩

-- High temperature at `β = β_c / 2`.
example : Summable (plusCorr 2 (Ising.betaC 2 / 2) (Percolation.origin 2)) :=
  (ising_sharp_phase_transition le_rfl).2.1 _ (by linarith [betaC_two_pos])
    (by linarith [betaC_two_pos])

-- Low temperature, `β = 2β_c`: `m*(2β_c) ≥ √3 / 2 > 0`.
example : Real.sqrt 3 / 2 ≤ magnetization 2 (2 * Ising.betaC 2) ∧
    0 < magnetization 2 (2 * Ising.betaC 2) := by
  have hpos := betaC_two_pos
  have h := (ising_sharp_phase_transition le_rfl).1 (2 * Ising.betaC 2) (by linarith)
  have hratio : Ising.betaC 2 / (2 * Ising.betaC 2) = 1 / 2 := by field_simp
  rw [hratio] at h
  have hs : Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) = Real.sqrt 3 / 2 := by
    rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs] at h
  exact ⟨h, lt_of_lt_of_le (by positivity) h⟩

-- At the critical point the lower bound is `0 ≤ m*(β_c)`.
example : 0 ≤ magnetization 2 (Ising.betaC 2) := by
  have h := (ising_sharp_phase_transition le_rfl).1 (Ising.betaC 2) le_rfl
  exact (Real.sqrt_nonneg _).trans h

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.IsingSharpnessUnconditional
