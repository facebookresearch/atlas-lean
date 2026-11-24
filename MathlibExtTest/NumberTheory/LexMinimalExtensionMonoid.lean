/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LexMinimalExtensionMonoid

open MetaMathlibExt

/-- An empty prefix forces the first summand to equal its zero competitor. -/
example {η₁ η₂ : ℕ → ℕ} (h : IsLexMinimalExtensionOf (η₁ + η₂) 0)
    (h₁ : IsBinomidIndex η₁) (h₂ : IsBinomidIndex η₂) : η₁ = 0 := by
  have hmin := (h.of_add h₁ h₂).1
  rcases hmin.2 _ (isBinomidIndex_const 0) (by simp) with heq | ⟨j, _, hj⟩
  · exact heq
  · exact (Nat.not_lt_zero _ hj).elim

/-- The sequence 0, 1, 2, … can be replaced by zero after its first entry. -/
example {η : ℕ → ℕ} (hη : IsBinomidIndex η) :
    ¬ IsLexMinimalExtensionOf (η + fun i => i) 1 := by
  intro h
  have hmin := (h.of_add hη (isBinomidIndex_of_monotone monotone_id)).2
  rcases hmin.2 _ (isBinomidIndex_const 0) (by simp) with heq | ⟨j, _, hj⟩
  · exact Nat.one_ne_zero (congrFun heq 1)
  · exact Nat.not_lt_zero _ hj

/-- There are no maximizing positive indices in an empty prefix. -/
example (η : ℕ → ℕ) : maxAverageIndices η 0 = ∅ := by
  simp [maxAverageIndices]

/-- For the prefix `0, 2`, an odd length cannot attain its maximal average of one. -/
example {η : ℕ → ℕ} (hη : IsLexMinimalExtensionOf η 2) (h₀ : η 0 = 0) (h₁ : η 1 = 2)
    (k : ℕ) : binomidAverage η (2 * k + 1) ≠ 1 := by
  have h₂ : binomidAverage η 2 = 1 := by
    norm_num [binomidAverage, Finset.sum_range_succ, h₀, h₁]
  have hJ : maxAverageIndices η 2 = {2} := by
    have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    norm_num [maxAverageIndices, hI, Finset.filter_insert, Finset.filter_singleton,
      binomidAverage_one, h₀, h₂]
  intro heq
  have hd := hη.gcd_maxAverageIndices_dvd (i := 2 * k + 1) (by omega)
    ⟨2, by simp [hJ], heq.trans h₂.symm⟩
  simp [hJ] at hd

/-- The singleton containing zero generates the zero submonoid but fails independence. -/
example : ¬ IsAddMonoidBasis ({0} : Set ℕ) {0} :=
  fun h => h.zero_notMem rfl

/-- The constant two sequence splits into two nonzero constant one sequences. -/
example : ¬ IsAtomicBinomidIndex (fun _ => 2) := by
  intro h
  rcases h.2.2 _ _ (isBinomidIndex_const 1) (isBinomidIndex_const 1) rfl with hz | hz <;>
    exact Nat.one_ne_zero (congrFun hz 0)
