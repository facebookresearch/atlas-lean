/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PermutipleStringsExistsCarriesOfIsMotherGraphEdge

/-!
# Tests for carries of mother-graph edges

Concrete applications of the carry existence theorem, including boundary carries,
multiplier one, equal base and multiplier, and base one.
-/

namespace MathlibExtTest.NumberTheory.Digits.PermutipleStringsExistsCarriesOfIsMotherGraphEdge

open MetaMathlibExt

example : ∃ c₁ c₂ : ℕ, c₁ = 3 ∧ c₂ = 0 ∧ (5 : ℤ) * c₂ - c₁ = -3 := by
  obtain ⟨c₁, c₂, h₁, h₂, heq⟩ := exists_carries_of_isMotherGraphEdge 4 5 3 0 (by decide)
  exact ⟨c₁, c₂, by omega, by omega, by omega⟩

example : ∃ c₁ c₂ : ℕ, c₁ = 0 ∧ c₂ = 3 ∧ (5 : ℤ) * c₂ - c₁ = 15 := by
  obtain ⟨c₁, c₂, h₁, h₂, heq⟩ := exists_carries_of_isMotherGraphEdge 4 5 1 4 (by decide)
  exact ⟨c₁, c₂, by omega, by omega, by omega⟩

example : ∃ c₁ c₂ : ℕ, c₁ = 0 ∧ c₂ = 0 ∧ (10 : ℤ) * c₂ - c₁ = 0 := by
  obtain ⟨c₁, c₂, h₁, h₂, heq⟩ := exists_carries_of_isMotherGraphEdge 1 10 7 7 (by decide)
  exact ⟨c₁, c₂, by omega, by omega, by omega⟩

example : ∃ c₁ c₂ : ℕ, c₁ = 3 ∧ c₂ = 1 ∧ (4 : ℤ) * c₂ - c₁ = 1 := by
  obtain ⟨c₁, c₂, h₁, h₂, heq⟩ := exists_carries_of_isMotherGraphEdge 4 4 3 1 (by decide)
  exact ⟨c₁, c₂, by omega, by omega, by omega⟩

example : ∃ c₁ c₂ : ℕ, IsHoeySloaneStep 3 1 c₁ c₂ (0, 0) := by
  obtain ⟨c₁, c₂, h₁, h₂, heq⟩ := exists_carries_of_isMotherGraphEdge 3 1 0 0 (by decide)
  exact ⟨c₁, c₂, by omega, by omega, by decide, heq⟩

end MathlibExtTest.NumberTheory.Digits.PermutipleStringsExistsCarriesOfIsMotherGraphEdge
