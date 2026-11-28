/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonSubsetBoundedRepresentations
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for Sidon subsets with a bounded representation count -/

open AdditiveCombinatorics Finset
open MathlibExt.NumberTheory.SidonSubsetBoundedRepresentationsErdosProblem772Wanted

-- Both orders of 0 + 2 and the doubled summand 1 + 1 are counted.
example : orderedRepresentationCount (↑({0, 1, 2} : Finset ℕ) : Set ℕ) 2 = 3 := by
  rw [orderedRepresentationCount_coe_finset]
  decide

private lemma progression_not_sidon : ¬ (↑({0, 1, 2} : Finset ℕ) : Set ℕ).IsSidon := by
  intro hsidon
  rcases Set.isSidon_iff.mp hsidon 0 (by decide) 2 (by decide) 1 (by decide) 1 (by decide)
    (by decide) with h | h
  all_goals exact (by decide : (0 : ℕ) ≠ 1) h.1

private lemma four_terms_not_sidon : ¬ (↑({0, 1, 4, 5} : Finset ℕ) : Set ℕ).IsSidon := by
  intro hsidon
  rcases Set.isSidon_iff.mp hsidon 0 (by decide) 5 (by decide) 1 (by decide) 4 (by decide)
    (by decide) with h | h
  · exact (by decide : (0 : ℕ) ≠ 1) h.1
  · exact (by decide : (0 : ℕ) ≠ 4) h.1

-- An independent witness for the quantitative bound at n = k = 3.
example : ∃ S ⊆ ({0, 1, 2} : Finset ℕ), (S : Set ℕ).IsSidon ∧
    (3 : ℝ) ^ ((2 : ℝ) / 3) / (8 * 3) ≤ S.card := by
  refine ⟨{0}, by decide, Set.isSidon_iff.mpr ?_, ?_⟩
  · simp
  · simp only [card_singleton, Nat.cast_one]
    apply (div_le_iff₀ (by norm_num)).2
    calc
      _ ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ _ := by norm_num

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
  exact progression_not_sidon hsidon

-- The full set also cannot survive a collision between four distinct summands.
example : ∃ S ⊆ ({0, 1, 4, 5} : Finset ℕ), 0 < S.card ∧ S ≠ {0, 1, 4, 5} := by
  obtain ⟨S, hSA, hsidon, hpos⟩ := quantitative_nonempty (A := {0, 1, 4, 5}) (by decide)
  refine ⟨S, hSA, hpos, ?_⟩
  rintro rfl
  exact four_terms_not_sidon hsidon

-- The corollary proves the named proposition without restating its body.
example : sidonSubsetBeyondSqrt := sidonSubsetBeyondSqrt_holds
