/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GraphRestrictedSumProductErdosProblem808

open MathlibExt.Combinatorics.GraphRestrictedSumProductErdosProblem808Wanted

-- The two-label example has eight different edges, seven sums and only four products.
example :
    let E : Finset (ℕ × ℕ) :=
      {(2, 18), (2, 24), (8, 18), (8, 24), (1, 36), (1, 48), (4, 36), (4, 48)}
    (∀ e ∈ E, 0 < e.1 ∧ e.1 < e.2) ∧ E.card = 8 ∧
      (E.image fun e => e.1 + e.2).card = 7 ∧
      (E.image fun e => e.1 * e.2).card = 4 := by decide

-- Recover the cofinal family of strict counterexamples from the public theorem.
example : ∃ c > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ᶠ n : ℕ in Filter.atTop,
    ∃ A : Finset ℕ, 0 ∉ A ∧ A.card = n ∧ ∃ E : Finset (ℕ × ℕ),
      (∀ p ∈ E, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2) ∧
      (n : ℝ) ^ (1 + c) ≤ E.card ∧
      max ((E.image fun p => p.1 + p.2).card : ℝ) ((E.image fun p => p.1 * p.2).card : ℝ) <
        (n : ℝ) ^ (1 + c - ε) := by
  have h := restrictedSumProductAlongGraphs_refuted
  unfold restrictedSumProductAlongGraphs at h
  push Not at h
  obtain ⟨c, ε, hc, hε, h⟩ := h
  exact ⟨c, hc, ε, hε, h⟩
