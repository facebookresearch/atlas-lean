/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NicomacheanTwoValuedLargeGap
import Mathlib.Tactic.NormNum

/-! # Tests for two-valued Nicomachean sequences with a large normalized gap -/

open MetaMathlibExt

-- The construction at n = 3 gives a gap of 6 in a list of length 10.
example :
    let σ := List.replicate 3 (3 : ℤ) ++ List.replicate 7 9
    nicomacheanNu σ = 0 ∧ (3 : ℤ) ∈ σ ∧ (9 : ℤ) ∈ σ ∧
      (1 : ℝ) / 2 < ((9 - 3 : ℤ) : ℝ) / σ.length := by
  dsimp only
  refine ⟨by decide, by decide, by decide, ?_⟩
  norm_num [List.length_append, List.length_replicate]

example :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ ∃ σ : List ℤ, (∀ x ∈ σ, x = a ∨ x = b) ∧ a ∈ σ ∧ b ∈ σ ∧
      nicomacheanNu σ = 0 ∧ 1 - (1 / 100 : ℝ) < ((b - a : ℤ) : ℝ) / σ.length :=
  exists_two_valued_nicomachean_large_gap (by norm_num)
