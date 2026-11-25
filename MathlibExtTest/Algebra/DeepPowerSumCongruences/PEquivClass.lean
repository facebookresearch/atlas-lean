/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.PEquivClass
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-! # Tests for $p$-equivalence classes of partitions and their class sums -/

open MetaMathlibExt

-- Splitting the part `3 = 3 * 1` of `(3, 2)` into three parts `1` gives `(2, 1, 1, 1)`.
example : IsPSplitting 3 {2, 1, 1, 1} {3, 2} :=
  ⟨1, le_rfl, by decide, by decide⟩

-- No part of `(2, 1)` is a multiple of `3`, so `(2, 1)` has no `3`-splitting.
example (s : Multiset ℕ) : ¬ IsPSplitting 3 s {2, 1} := by
  rintro ⟨u, hu, hmem, -⟩
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
  omega

-- `(1, 1, 1)` lies in the `3`-equivalence class of `(3)`.
example : (⟨{1, 1, 1}, by decide, by decide⟩ : Nat.Partition ({3} : Multiset ℕ).sum) ∈
    pEquivClass 3 {3} := by
  simp only [pEquivClass, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Relation.EqvGen.rel _ _ (isPSplitting_replicate_singleton 3 le_rfl)

-- For `p = 3` and `λ = (3)` the common sign is `(-1) ^ (3 - 1) = 1`.
example (σ : Type*) [Fintype σ] :
    pEquivClassSum σ 3 {3} = ∑ μ ∈ pEquivClass 3 {3}, (1 /
      ((μ.parts.toFinset.prod fun a => a ^ μ.parts.count a * (μ.parts.count a).factorial :
        ℕ) : ℚ)) • (μ.parts.map (MvPolynomial.psum σ ℚ)).prod := by
  simpa using pEquivClassSum_eq_neg_one_pow_smul σ (p := 3) (by decide)
    (⟨{3}, by simp, by simp⟩ : Nat.Partition 3)

-- For `p = 3` and `λ = (2, 1)` the common sign is `(-1) ^ (3 - 2) = -1`.
example (σ : Type*) [Fintype σ] :
    pEquivClassSum σ 3 {2, 1} = -∑ μ ∈ pEquivClass 3 {2, 1}, (1 /
      ((μ.parts.toFinset.prod fun a => a ^ μ.parts.count a * (μ.parts.count a).factorial :
        ℕ) : ℚ)) • (μ.parts.map (MvPolynomial.psum σ ℚ)).prod := by
  simpa using pEquivClassSum_eq_neg_one_pow_smul σ (p := 3) (by decide)
    (⟨{2, 1}, by simp, by simp⟩ : Nat.Partition 3)

-- The prime must be odd. For `p = 2` and `λ = (2)` the class contains `(2)` and `(1, 1)`, whose
-- signs differ: in one variable, evaluating at `x = 1` turns the difference of the two sides into
-- a sum of nonnegative terms, the term of `(1, 1)` being `1`.
example : ¬ ∀ {n : ℕ} (l : n.Partition), pEquivClassSum Unit 2 l.parts =
    ((-1 : ℚ) ^ (n - Multiset.card l.parts)) • ∑ μ ∈ pEquivClass 2 l.parts, (1 /
      ((μ.parts.toFinset.prod fun a => a ^ μ.parts.count a * (μ.parts.count a).factorial :
        ℕ) : ℚ)) • (μ.parts.map (MvPolynomial.psum Unit ℚ)).prod := by
  intro h
  have h2 := congrArg (MvPolynomial.eval fun _ => (1 : ℚ))
    (h (⟨{2}, by simp, by simp⟩ : Nat.Partition 2))
  simp only [pEquivClassSum, map_sum, MvPolynomial.smul_eval, map_multiset_prod,
    Multiset.map_map, Function.comp_def, MvPolynomial.psum, Finset.univ_unique,
    Finset.sum_singleton, map_pow, MvPolynomial.eval_X, one_pow, Multiset.map_const',
    Multiset.prod_replicate, mul_one, Multiset.card_singleton, Nat.reduceSub, pow_one,
    neg_one_mul, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib] at h2
  refine (Finset.sum_pos' (fun μ _ => ?_) ⟨⟨{1, 1}, by decide, by decide⟩, ?_, ?_⟩).ne' h2
  · rw [← add_div]
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    rcases neg_one_pow_eq_or ℚ (({2} : Multiset ℕ).sum - Multiset.card μ.parts) with h | h <;>
      rw [h] <;> norm_num
  · simp only [pEquivClass, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.EqvGen.rel _ _ (isPSplitting_replicate_singleton 2 le_rfl)
  · have hz : (({1, 1} : Multiset ℕ).toFinset.prod fun a =>
        a ^ ({1, 1} : Multiset ℕ).count a * (({1, 1} : Multiset ℕ).count a).factorial) = 2 := by
      decide
    dsimp only
    rw [hz]
    norm_num
