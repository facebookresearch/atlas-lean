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

-- The gaps of {3, 4} are 1, 2 and 5. Playing either smaller gap generates 5.
example : 5 ∉ sylverLegalMoves (insert 2 {3, 4}) := by
  have hF : IsGreatest (sylverLegalMoves {3, 4}) 5 :=
    frobeniusNumber_pair (m := 3) (n := 4) (by decide) (by decide) (by decide)
  have htwo : 2 ∈ sylverLegalMoves {3, 4} := by
    simp only [sylverLegalMoves, Set.mem_ofPred_eq, AddSubmonoid.mem_closure_pair, smul_eq_mul]
    omega
  apply sylverEnder_eliminates_largest_move hF ?_ (by decide) 2 htwo (by decide)
  intro y hy
  by_contra hne
  have hlt := lt_of_le_of_ne (hF.2 hy.1) hne
  have hpos : y ≠ 0 := fun h => zero_notMem_sylverLegalMoves _ (h ▸ hy.1)
  have hnot : y ∉ ({3, 4} : Set ℕ) := fun h => hy.1 (AddSubmonoid.subset_closure h)
  have hcomp : 5 - y ∈ ({3, 4} : Set ℕ) := by
    simp at hnot ⊢
    omega
  apply hy.2 5 hF.1 (Ne.symm hne)
  have hsum := add_mem (AddSubmonoid.subset_closure (Set.mem_insert y ({3, 4} : Set ℕ)))
    (AddSubmonoid.subset_closure (Set.mem_insert_of_mem y hcomp))
  simpa [Nat.add_sub_of_le hlt.le] using hsum
