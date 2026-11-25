/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem844

/-! # Tests for Erdős Problem 844 and Chvátal's theorem for shifted down-sets -/

namespace MathlibExt.NumberTheory.ErdosProblem844Wanted

-- The extremal set for `N = 10`: the even numbers together with the odd non-squarefree `9`.
example : evenOrOddNonSquarefree 10 = {2, 4, 6, 8, 9, 10} := by decide +kernel

-- `1` never belongs to the extremal set, matching the case `a = b = 1` of the condition.
example (N : ℕ) : 1 ∉ evenOrOddNonSquarefree N := by
  simp [evenOrOddNonSquarefree]

-- No set in `{1, ..., 10}` whose pairwise products (squares included) are non-squarefree has more
-- than six elements.
example (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 10)
    (h : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) : A.card ≤ 6 := by
  have hbound := (conjecture_holds 10).2 ⟨A, hA, h, rfl⟩
  rwa [show (evenOrOddNonSquarefree 10).card = 6 by decide +kernel] at hbound

-- The bound for `N = 10` is attained.
example : ∃ A ⊆ Finset.Icc 1 10, (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) ∧ A.card = 6 := by
  have hmem := (conjecture_holds 10).1
  rwa [show (evenOrOddNonSquarefree 10).card = 6 by decide +kernel] at hmem

-- For `N = 1` the bound is `0`: the set `{1}` is excluded because `1 * 1` is squarefree.
example (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 1)
    (h : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) : A = ∅ := by
  have hbound := (conjecture_holds 1).2 ⟨A, hA, h, rfl⟩
  rw [show evenOrOddNonSquarefree 1 = ∅ by decide +kernel] at hbound
  simpa using hbound

/-- The subsets of `{0, 1, 2}` with at most two elements: a shifted down-set. -/
private def smallFamily : Finset (Finset ℕ) := (Finset.range 3).powerset.filter (·.card ≤ 2)

private lemma isLowerSet_smallFamily : IsLowerSet (smallFamily : Set (Finset ℕ)) := by
  intro A B hBA hA
  simp only [smallFamily, Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hA ⊢
  exact ⟨Finset.Subset.trans hBA hA.1, (Finset.card_le_card hBA).trans hA.2⟩

private lemma shift_smallFamily :
    ∀ A ∈ smallFamily, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ smallFamily := by
  decide

-- Chvátal's bound in `smallFamily`: the star of `0` has three members, so every intersecting
-- subfamily has at most three members.
example (𝓐 : Finset (Finset ℕ)) (h𝓐 : 𝓐 ⊆ smallFamily)
    (hint : (𝓐 : Set (Finset ℕ)).Intersecting) : 𝓐.card ≤ 3 := by
  have hbound := card_le_card_filter_zero_mem isLowerSet_smallFamily shift_smallFamily h𝓐 hint
  rwa [show (smallFamily.filter (0 ∈ ·)).card = 3 by decide] at hbound

-- The bound is also attained by the triangle `{{0, 1}, {0, 2}, {1, 2}}`, which is not a star.
example : (({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)) : Set (Finset ℕ)).Intersecting ∧
    ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)) ⊆ smallFamily ∧
    ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)).card = 3 := by
  refine ⟨?_, by decide, by decide⟩
  simp only [Set.Intersecting, Finset.mem_coe]
  decide

end MathlibExt.NumberTheory.ErdosProblem844Wanted
