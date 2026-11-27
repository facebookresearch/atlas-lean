/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.HindmanFiniteSums

/-!
# Pairwise sum theorem

Hindman's finite sums theorem gives an infinite set whose nonempty finite subsets all have
sums of the same color. Singletons give the colors of the members, and two-element subsets
give the colors of sums of distinct members.
-/

namespace MetaMathlibExt

/-- **Pairwise sum theorem.** For every finite coloring of $\mathbb{N} = \{0, 1, 2, \dots\}$ there
is an infinite set $A \subseteq \mathbb{N}$ such that $A \cup \{a + a' : a, a' \in A, a \ne a'\}$
is monochromatic.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 1.2 (`integers-2025-A105-thm-1-2`). -/
public theorem exists_infinite_pairwiseSums_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ k : Fin r, (∀ a ∈ A, c a = k) ∧
      ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → c (a + a') = k := by
  obtain ⟨A, hA, k, hsum⟩ := exists_infinite_finiteSums_monochromatic c
  refine ⟨A, hA, k, ?_, ?_⟩
  · intro a ha
    simpa using hsum {a} (Finset.singleton_nonempty a) (by simpa using ha)
  · intro a ha b hb hab
    simpa [Finset.sum_pair hab] using
      hsum {a, b} (Finset.insert_nonempty a {b}) (by simp [Set.insert_subset_iff, ha, hb])

end MetaMathlibExt
