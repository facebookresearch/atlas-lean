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

/-- The singleton containing zero generates the zero submonoid but fails independence. -/
example : ¬ IsAddMonoidBasis ({0} : Set ℕ) {0} :=
  fun h => h.zero_notMem rfl

/-- The constant two sequence splits into two nonzero constant one sequences. -/
example : ¬ IsAtomicBinomidIndex (fun _ => 2) := by
  intro h
  rcases h.2.2 _ _ (isBinomidIndex_const 1) (isBinomidIndex_const 1) rfl with hz | hz <;>
    exact Nat.one_ne_zero (congrFun hz 0)
