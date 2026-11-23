/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SylverCoinage
import Mathlib.NumberTheory.FrobeniusNumber

open MetaMathlibExt

-- In the position {2, 3}, erasing either generator makes that number legal again.
example : {s | s ∈ AddSubmonoid.closure ({2, 3} : Set ℕ) ∧ s ≠ 0 ∧
    ∀ a ∈ AddSubmonoid.closure ({2, 3} : Set ℕ), ∀ b ∈ AddSubmonoid.closure ({2, 3} : Set ℕ),
      a + b = s → a = 0 ∨ b = 0} = ({2, 3} : Set ℕ) := by
  have hcanon (a : ℕ) (ha : a ∈ ({2, 3} : Finset ℕ)) :
      sylverLegalMoves ((({2, 3} : Finset ℕ).erase a) : Set ℕ) ≠ sylverLegalMoves {2, 3} := by
    have hplayed : a ∉ sylverLegalMoves {2, 3} :=
      fun h => h (AddSubmonoid.subset_closure (by simpa using ha))
    intro heq
    apply hplayed
    rw [← heq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;>
      simp [sylverLegalMoves, AddSubmonoid.mem_closure_singleton, smul_eq_mul] <;> omega
  have hF : FrobeniusNumber 1 ({2, 3} : Set ℕ) :=
    frobeniusNumber_pair (m := 2) (n := 3) (by decide) (by decide) (by decide)
  have hfin : (sylverLegalMoves {2, 3}).Finite := (Set.finite_le_nat 1).subset hF.2
  apply Eq.symm
  simpa using sylverPosition_canonical_eq_minimalGenerators {2, 3}
    (by simpa using hcanon) (by simpa using hfin)

-- Adding zero leaves the legal moves unchanged, so a position containing zero is redundant.
example (M : Set ℕ) : sylverLegalMoves (insert 0 M) = sylverLegalMoves M := by
  simp [sylverLegalMoves]
