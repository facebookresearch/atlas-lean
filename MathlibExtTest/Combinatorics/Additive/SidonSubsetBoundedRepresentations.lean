/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonSubsetBoundedRepresentations

/-! # Tests for Sidon subsets with a bounded representation count -/

open AdditiveCombinatorics Filter
open MathlibExt.NumberTheory.SidonSubsetBoundedRepresentationsErdosProblem772Wanted

-- The threshold is uniform in the choice of the ambient set.
example : ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A.card = n →
    (∀ m, orderedRepresentationCount (A : Set ℕ) m ≤ 3) →
    ∃ S ⊆ A, (S : Set ℕ).IsSidon ∧ 2 * Real.sqrt n ≤ S.card :=
  sidonSubsetBeyondSqrt_holds 3 (by decide) 2

-- The Sidon subset excludes nontrivial three-term progressions, not just
-- collisions between pairs of distinct summands.
example : ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A.card = n →
    (∀ m, orderedRepresentationCount (A : Set ℕ) m ≤ 3) →
    ∃ S ⊆ A, Real.sqrt n ≤ S.card ∧ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + c = b + b → a = b ∧ c = b := by
  filter_upwards [sidonSubsetBeyondSqrt_holds 3 (by decide) 1] with n hn A hA hrep
  obtain ⟨S, hSA, hsidon, hcard⟩ := hn A hA hrep
  refine ⟨S, hSA, by simpa using hcard, ?_⟩
  intro a ha b hb c hc hsum
  exact (hsidon a ha c hc b hb b hb hsum).elim id id
