/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DistinctPartialSumsOrdering
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

open MathlibExt.Combinatorics.ValidOrderingWanted

-- The empty set has the empty ordering, whose list of partial sums is empty.
example : ∃ l : List ℤ, l.Perm (∅ : Finset ℤ).toList ∧ (l.scanl (· + ·) 0).tail.Nodup :=
  exists_distinct_partial_sums_ordering ∅ (by simp)

-- The partial sums of a valid ordering of `A` take exactly `|A|` values.
example (A : Finset ℤ) (h0 : 0 ∉ A) :
    ∃ l : List ℤ, l.Perm A.toList ∧ (l.scanl (· + ·) 0).tail.toFinset.card = A.card := by
  obtain ⟨l, hl, hnd⟩ := exists_distinct_partial_sums_ordering A h0
  refine ⟨l, hl, ?_⟩
  rw [List.toFinset_card_of_nodup hnd, List.length_tail, List.length_scanl, hl.length_eq,
    Finset.length_toList, Nat.add_sub_cancel]

-- The set `{6, 1, -7}` has a valid ordering, for instance `6, 1, -7` with partial sums `6, 7, 0`.
example : ∃ l : List ℤ, l.Perm ({6, 1, -7} : Finset ℤ).toList ∧
    (l.scanl (· + ·) 0).tail.Nodup :=
  exists_distinct_partial_sums_ordering _ (by decide)

example : ([6, 1, -7].scanl (· + ·) 0).tail = [6, 7, 0] ∧
    ([6, 1, -7].scanl (· + ·) 0).tail.Nodup := by
  simp

-- The empty partial sum must not be counted: `{6, 1, -7}` sums to `0`, so the last partial sum
-- of every ordering is `0` again.
example (l : List ℤ) (hl : l.Perm ({6, 1, -7} : Finset ℤ).toList) :
    ¬ (l.scanl (· + ·) 0).Nodup := by
  have hlen : l.length = 3 := by
    rw [hl.length_eq, Finset.length_toList]
    decide
  have hsum : l.sum = 0 := by
    rw [hl.sum_eq, Finset.sum_toList]
    decide
  intro hnd
  have h3 : (l.scanl (· + ·) 0)[3]'(by simp [hlen]) = (l.scanl (· + ·) 0)[0]'(by simp) := by
    rw [List.getElem_scanl, List.getElem_scanl_zero, ← hlen, List.take_length, ← List.sum_eq_foldl,
      hsum]
  exact absurd ((hnd.getElem_inj_iff).mp h3) (by decide)
