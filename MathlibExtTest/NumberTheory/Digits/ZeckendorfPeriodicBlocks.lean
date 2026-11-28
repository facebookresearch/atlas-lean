/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfPeriodicBlocks

/-! # Tests for decomposition of proper blocks in nested Zeckendorf collections -/

open MetaMathlibExt

private def digits (j : ℕ) : ℕ := if j = 1 then 1 else 0

private def intervals : Set (ℕ × ℕ) := {(1, 2), (3, 3)}

private theorem proper_digits : IsProperLStarBlock [1, 0] digits 1 3 := by
  apply isProperLStarBlock_iff.mpr
  refine ⟨by decide, ?_, by decide, ?_⟩
  · intro j hj
    have h : j = 1 ∨ j = 2 := by
      obtain ⟨h₁, h₂⟩ := hj
      omega
    rcases h with rfl | rfl <;> decide
  · intro j hj
    have h : j = 1 := by
      by_contra hn
      exact hj (ite_eq_right hn)
    subst j
    exact ⟨by decide, by decide⟩

-- Compute the disjoint decomposition without using Lemma 9. The interval ending at 3
-- is present even though its digit is zero, and the interval [1, 2] has a nonempty prefix.
example : IsLStarBlockSum [1, 1] intervals digits ∧ (∀ p ∈ intervals, p.2 ≤ 3) ∧
    (3, 3) ∈ intervals ∧ digits 3 = 0 := by
  refine ⟨isLStarBlockSum_iff.mpr ⟨?_, ?_, ?_⟩, ?_, by simp [intervals], by decide⟩
  · intro p hp q hq hne
    simp only [intervals, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (hne rfl).elim
    · exact Set.disjoint_left.mpr fun j hj hk => (show j ≤ 2 from hj.2).not_gt
        (show 2 < j from lt_of_lt_of_le (by decide) hk.1)
    · exact Set.disjoint_left.mpr fun j hj hk => (show j ≤ 2 from hk.2).not_gt
        (show 2 < j from lt_of_lt_of_le (by decide) hj.1)
    · exact (hne rfl).elim
  · intro p hp
    simp only [intervals, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · refine ⟨by decide, ?_, by decide⟩
      intro j hj
      have heq : j = 1 := by
        obtain ⟨h₁, h₂⟩ := hj
        omega
      subst j
      decide
    · refine ⟨by decide, ?_, by decide⟩
      intro j hj
      exact (hj.2.not_ge hj.1).elim
  · intro j hj
    have heq : j = 1 := by
      by_contra hn
      exact hj (ite_eq_right hn)
    subst j
    exact Set.mem_iUnion₂.mpr ⟨(1, 2), by simp [intervals], ⟨by decide, by decide⟩⟩
  · intro p hp
    simp only [intervals, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> decide

-- The public lemma accepts the same proper block when the pair is assumed nested.
example (hsub : periodicZeckendorfCollection [1, 0] ⊂ periodicZeckendorfCollection [1, 1]) :
    ∃ I, IsLStarBlockSum [1, 1] I digits ∧ (∀ p ∈ I, p.2 ≤ 3) ∧ ∃ a, (a, 3) ∈ I :=
  exists_lStarBlockSum_of_properLStarBlock [1, 0] [1, 1] (by decide) (by decide) (by decide)
    (by decide) hsub proper_digits (fun h => by simpa [digits] using congrFun h 1)
