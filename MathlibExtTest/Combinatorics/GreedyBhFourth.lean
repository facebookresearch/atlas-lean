/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GreedyBhFourth
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.GreedyBhFourth` -/

namespace MathlibExtTest.GreedyBhFourth

open AdditiveCombinatorics MathlibExt.Combinatorics.GreedyBhFourthWanted

-- Test section: values of the quasipolynomial. For `h = 1, …, 5` the fourth greedy terms are
-- `4, 12, 32, 55, 108`; `h = 2` is the term `12` of the greedy Sidon set `0, 1, 3, 7, 12, …`.
example : fourthValue 1 = 4 := by decide
example : fourthValue 2 = 12 := by decide
example : fourthValue 3 = 32 := by decide
example : fourthValue 4 = 55 := by decide
example : fourthValue 5 = 108 := by decide

-- The floor-function form `⌊(h + 3)/2⌋ h² + ⌊3h/2⌋ + 1` of the same quasipolynomial, for `h < 40`.
example : ∀ h < 40, fourthValue h = (h + 3) / 2 * h ^ 2 + 3 * h / 2 + 1 := by decide

-- Test section: the upper bound. For the greedy Sidon set (`h = 2`) the fourth term is at most
-- `12`, so `13` is never the fourth greedy term.
example (a : ℕ) (ha : IsFourthGreedyBh 2 a) : a ≤ 12 :=
  (isFourthGreedyBh_le_fourthValue 2 a two_pos ha).trans_eq (by decide)

example : ¬IsFourthGreedyBh 2 13 := fun h =>
  absurd (isFourthGreedyBh_le_fourthValue 2 13 two_pos h) (by decide)

-- The lower bound rejects the candidates just below the even and odd bounds.
example : ¬ IsFourthGreedyBh 2 11 := fun h =>
  absurd (fourthValue_le_of_isFourthGreedyBh 2 11 (by decide) h) (by decide)

example : ¬ IsFourthGreedyBh 3 31 := fun h =>
  absurd (fourthValue_le_of_isFourthGreedyBh 3 31 (by decide) h) (by decide)

-- The greedy step rejects `2` after `{0, 1}` for `h = 2`, since `0 + 2 = 1 + 1`.
example : ¬IsNextGreedyBh 2 {0, 1} 2 := by
  intro H
  have m₁ : ∀ x ∈ ([0, 2] : List ℕ), x ∈ (insert 2 {0, 1} : Set ℕ) := by decide
  have m₂ : ∀ x ∈ ([1, 1] : List ℕ), x ∈ (insert 2 {0, 1} : Set ℕ) := by decide
  exact (by decide : ¬([0, 2] : List ℕ).Perm [1, 1])
    (H.2.1.2.2 [0, 2] [1, 1] m₁ m₂ rfl rfl (by decide) (by decide) rfl)

-- Test section: the edge case `h = 1`. Every nonempty set of natural numbers is a `B_1`-set, so
-- the greedy `B_1`-set is `0, 1, 2, …`: the hypothesis of the upper bound holds for `a = 4`, and
-- the bound `fourthValue 1 = 4` is attained.
private theorem isBhSet_one {A : Set ℕ} (hA : A.Nonempty) : IsBhSet A 1 := by
  refine ⟨hA, one_pos, ?_⟩
  intro l₁ l₂ _ _ hl₁ hl₂ e₁ e₂ hsum
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hl₁
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 hl₂
  have hxy : x = y := hsum
  rw [hxy]

private theorem isNextGreedyBh_one {A : Set ℕ} {a : ℕ} (hA : ∀ x ∈ A, x < a)
    (hmax : a - 1 ∈ A) : IsNextGreedyBh 1 A a :=
  ⟨hA, isBhSet_one ⟨a, Set.mem_insert a A⟩, fun b hb hba => by
    have := hb (a - 1) hmax
    omega⟩

example : IsFourthGreedyBh 1 4 := by
  refine ⟨isNextGreedyBh_one ?_ ?_, isNextGreedyBh_one ?_ ?_, isNextGreedyBh_one ?_ ?_,
    isNextGreedyBh_one ?_ ?_⟩ <;> norm_num

example (a : ℕ) (ha : IsFourthGreedyBh 1 a) : a ≤ 4 :=
  (isFourthGreedyBh_le_fourthValue 1 a one_pos ha).trans_eq (by decide)

end MathlibExtTest.GreedyBhFourth
