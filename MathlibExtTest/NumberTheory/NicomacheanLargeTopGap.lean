/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NicomacheanLargeTopGap

/-! # Tests for Nicomachean sequences with a large gap at the top -/

open MetaMathlibExt

example :
    ∃ σ : List ℤ, (∀ x ∈ σ, 0 < x) ∧ nicomacheanNu σ = 0 ∧ ∃ a ∈ σ, ∃ b ∈ σ,
      σ.count b = 1 ∧ (∀ x ∈ σ, x ≤ b) ∧ a < b ∧ (∀ x ∈ σ, x ≠ b → x ≤ a) ∧
        (0 : ℤ) < b - a :=
  exists_nicomachean_large_top_gap 0

example :
    ∃ σ : List ℤ, nicomacheanNu σ = 0 ∧ ∃ a ∈ σ, ∃ b ∈ σ,
      σ.count b = 1 ∧ (∀ x ∈ σ, x ≠ b → x + 100 < b) := by
  obtain ⟨σ, _, hν, a, ha, b, hb, hcount, _, _, hrest, hgap⟩ :=
    exists_nicomachean_large_top_gap 100
  refine ⟨σ, hν, a, ha, b, hb, hcount, ?_⟩
  intro x hx hxb
  have hxa := hrest x hx hxb
  omega
