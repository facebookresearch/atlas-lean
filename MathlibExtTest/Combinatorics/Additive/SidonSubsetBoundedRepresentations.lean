/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonSubsetBoundedRepresentations
import Mathlib.Tactic.Positivity

/-! # Tests for Sidon subsets with a bounded representation count -/

open AdditiveCombinatorics Filter Finset
open MathlibExt.NumberTheory.SidonSubsetBoundedRepresentationsErdosProblem772Wanted

-- Both orders of 0 + 2 and the doubled summand 1 + 1 are counted.
example : orderedRepresentationCount (↑({0, 1, 2} : Finset ℕ) : Set ℕ) 2 = 3 := by
  rw [orderedRepresentationCount_coe_finset]
  decide

-- For a fixed sum, the second summand is determined by the first.
private lemma reps_le_card (A : Finset ℕ) (m : ℕ) :
    orderedRepresentationCount (A : Set ℕ) m ≤ A.card := by
  rw [orderedRepresentationCount_coe_finset]
  refine card_le_card_of_injOn Prod.fst (fun p hp => (mem_filter.mp hp).2.1) ?_
  intro p hp q hq heq
  have hp' := mem_antidiagonal.mp (mem_filter.mp hp).1
  have hq' := mem_antidiagonal.mp (mem_filter.mp hq).1
  exact Prod.ext heq (by omega)

private lemma quantitative_nonempty {A : Finset ℕ} (hA : 0 < A.card) :
    ∃ S ⊆ A, (S : Set ℕ).IsSidon ∧ 0 < S.card := by
  obtain ⟨S, hSA, hsidon, hcard⟩ := exists_sidon_card_rpow hA hA (reps_le_card A)
  have hA' : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hpos := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos hA' _) (by positivity)) hcard
  exact ⟨S, hSA, hsidon, by exact_mod_cast hpos⟩

-- A nonempty subset is guaranteed, but the full three-term progression cannot survive.
example : ∃ S ⊆ ({0, 1, 2} : Finset ℕ), 0 < S.card ∧ S ≠ {0, 1, 2} := by
  obtain ⟨S, hSA, hsidon, hpos⟩ := quantitative_nonempty (A := {0, 1, 2}) (by decide)
  refine ⟨S, hSA, hpos, ?_⟩
  rintro rfl
  rcases hsidon 0 (by decide) 2 (by decide) 1 (by decide) 1 (by decide) (by decide) with h | h
  all_goals exact (by decide : (0 : ℕ) ≠ 1) h.1

-- The full set also cannot survive a collision between four distinct summands.
example : ∃ S ⊆ ({0, 1, 4, 5} : Finset ℕ), 0 < S.card ∧ S ≠ {0, 1, 4, 5} := by
  obtain ⟨S, hSA, hsidon, hpos⟩ := quantitative_nonempty (A := {0, 1, 4, 5}) (by decide)
  refine ⟨S, hSA, hpos, ?_⟩
  rintro rfl
  rcases hsidon 0 (by decide) 5 (by decide) 1 (by decide) 4 (by decide) (by decide) with h | h
  · exact (by decide : (0 : ℕ) ≠ 1) h.1
  · exact (by decide : (0 : ℕ) ≠ 4) h.1

-- The asymptotic corollary supplies one threshold for every ambient set of size n.
example : ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A.card = n →
    (∀ m, orderedRepresentationCount (A : Set ℕ) m ≤ 3) →
    ∃ S ⊆ A, Real.sqrt n ≤ S.card ∧ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a + c = b + b → a = b ∧ c = b := by
  filter_upwards [sidonSubsetBeyondSqrt_holds 3 (by decide) 1] with n hn A hA hrep
  obtain ⟨S, hSA, hsidon, hcard⟩ := hn A hA hrep
  refine ⟨S, hSA, by simpa using hcard, ?_⟩
  intro a ha b hb c hc hsum
  exact (hsidon a ha c hc b hb b hb hsum).elim id id
