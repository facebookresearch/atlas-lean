/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidAverage

open MetaMathlibExt

/-- At block length one, each later entry dominates the first entry. -/
example {η : ℕ → ℕ} (hη : IsBinomidIndex η) (n : ℕ) : η 0 ≤ η (n + 1) := by
  have h := (hη.binomidAverage_props (i := 1) (l := n + 1) le_rfl (by omega)).1
  simpa [binomidAverage, add_comm 1 (n + 1)] using h

/-- Initial entries one and four give the fractional lower bound 5/2 at every even length. -/
example {η : ℕ → ℕ} (hη : IsBinomidIndex η) (h₀ : η 0 = 1) (h₁ : η 1 = 4)
    {k : ℕ} (hk : 1 ≤ k) : 5 / 2 ≤ binomidAverage η (k * 2) := by
  have h := (hη.binomidAverage_props (i := 2) (l := 1) (by decide) le_rfl).2.1 k hk
  have havg : binomidAverage η 2 = 5 / 2 := by
    simp [binomidAverage, Finset.sum_range_succ, h₀, h₁]
  rwa [havg] at h

/-- Appending one term to a two-term prefix gives the new term one third of the weight. -/
example {η : ℕ → ℕ} (hη : IsBinomidIndex η) :
    binomidAverage η 3 = (1 / 3) * η 2 + (2 / 3) * binomidAverage η 2 := by
  have h := (hη.binomidAverage_props (i := 1) (l := 2) le_rfl (by decide)).2.2
  norm_num at h ⊢
  exact h
