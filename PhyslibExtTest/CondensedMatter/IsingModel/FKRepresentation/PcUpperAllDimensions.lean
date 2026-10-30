/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperAllDimensions

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperAllDimensions`

* `fkPc_lt_one_of_two_le` at `(d, q) = (2, 2)`, `(3, 1)` (Bernoulli percolation) and `(2, 4)`, and
  together with `fkPc_pos_of_two_le` the bounds `0 < p_c(2, 2) < 1`;
* `ising_phase_transition_of_two_le` at `d = 2` and `d = 3`: both phases occur, i.e.
  there is `β > 0` with `m*(β) = 0` and `β` with `m*(β) > 0`;
* `isingBetaC_eq_fkPc_of_two_le` at `d = 2` and `d = 3`, with the consequence `0 < β_c`, and the
  agreement of `β_c` with the critical point of `ising_transition_at_fkPc_of_two_le`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.PcUpperAllDimensions

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.IsingFK _root_.StatMech.Ising

-- The FK critical point of the square lattice at `q = 2` is below one.
example : fkPc 2 2 < 1 := fkPc_lt_one_of_two_le le_rfl (by norm_num)

-- The critical point of Bernoulli bond percolation (`q = 1`) on `ℤ³` is below one.
example : fkPc 3 1 < 1 := fkPc_lt_one_of_two_le (by norm_num) le_rfl

-- The FK critical point of the square lattice at `q = 4` is below one.
example : fkPc 2 4 < 1 := fkPc_lt_one_of_two_le le_rfl (by norm_num)

-- The FK critical point at `q = 2` is nontrivial: `0 < p_c(2, 2) < 1`.
example : 0 < fkPc 2 2 ∧ fkPc 2 2 < 1 :=
  ⟨fkPc_pos_of_two_le le_rfl (by norm_num), fkPc_lt_one_of_two_le le_rfl (by norm_num)⟩

-- In `d = 2` both phases occur: zero magnetization at some `β > 0`, positive at some `β`.
example : (∃ β, 0 < β ∧ magnetization 2 β = 0) ∧ ∃ β, 0 < magnetization 2 β := by
  obtain ⟨βc, hβc, hlow, hhigh⟩ := ising_phase_transition_of_two_le (d := 2) le_rfl
  exact ⟨⟨βc / 2, by linarith, hlow _ (by linarith) (by linarith)⟩,
    ⟨βc + 1, hhigh _ (by linarith)⟩⟩

-- In `d = 3` both phases occur.
example : (∃ β, 0 < β ∧ magnetization 3 β = 0) ∧ ∃ β, 0 < magnetization 3 β := by
  obtain ⟨βc, hβc, hlow, hhigh⟩ := ising_phase_transition_of_two_le (d := 3) (by norm_num)
  exact ⟨⟨βc / 2, by linarith, hlow _ (by linarith) (by linarith)⟩,
    ⟨βc + 1, hhigh _ (by linarith)⟩⟩

-- The Ising critical point of `ℤ²` is the image of the FK critical point.
example : betaC (magnetization 2) = -(1 / 2) * Real.log (1 - fkPc 2 2) :=
  isingBetaC_eq_fkPc_of_two_le le_rfl

-- The Ising critical point of `ℤ³` is the image of the FK critical point.
example : isingBetaC 3 = -(1 / 2) * Real.log (1 - fkPc 3 2) :=
  isingBetaC_eq_fkPc_of_two_le (by norm_num)

-- Consequence: the Ising critical point of `ℤ²` is positive.
example : 0 < betaC (magnetization 2) := by
  rw [isingBetaC_eq_fkPc_of_two_le le_rfl, ← pToBeta_two]
  exact Ising.pToBeta_two_pos (fkPc_pos_of_two_le le_rfl (by norm_num))
    (fkPc_lt_one_of_two_le le_rfl (by norm_num))

-- `β_c` is the point where the magnetization switches on, as in the transition statement.
example : betaC (magnetization 2) = pToBeta 2 (fkPc 2 2) := by
  rw [isingBetaC_eq_fkPc_of_two_le le_rfl, pToBeta_two]

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.PcUpperAllDimensions
