/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelNonIntegralityExistsUniqueGobelASequence

/-! # Tests for `MathlibExt.NumberTheory.GobelNonIntegralityExistsUniqueGobelASequence` -/

namespace MathlibExtTest.NumberTheory.GobelNonIntegralityExistsUniqueGobelASequence

open MetaMathlibExt

-- The instance `p = 5`, `l = 2` satisfies the hypotheses.
example : ∃! a : ℕ → ℤ, IsGobelASequence 5 2 a :=
  existsUnique_gobelASequence 5 2 (by decide) (by decide) ⟨1, rfl⟩ (by decide)

-- The unique sequence has `a 1 = 1`, `a 0 = 0` and, by symmetry, `a 4 = 1`.
example : ∃ a : ℕ → ℤ, IsGobelASequence 5 2 a ∧ a 1 = 1 ∧ a 0 = 0 ∧ a 4 = 1 := by
  obtain ⟨a, ha, -⟩ :=
    existsUnique_gobelASequence 5 2 (by decide) (by decide) ⟨1, rfl⟩ (by decide)
  have hsym := ha.2.2.2.1 1 (by decide) (by decide)
  have h41 : (5 - 1 : ℕ) = 4 := by decide
  rw [h41] at hsym
  refine ⟨a, ha, ha.2.2.1, ha.2.1 0 (Or.inl rfl), hsym.symm.trans ha.2.2.1⟩

-- The admissible case `l = 0`: the period is one, so every index takes the zero-residue
-- branch of the periodic extension.
example (a a' : ℕ → ℤ) (ha : IsGobelASequence 5 0 a) (ha' : IsGobelASequence 5 0 a') :
    a = a' :=
  (existsUnique_gobelASequence 5 0 (by decide) (by decide) ⟨0, rfl⟩ (by decide)).unique ha ha'

-- For `p = 5`, `l = 0` the unique sequence is `1` on `1..4` and `0` at `5`.
example : ∃ a : ℕ → ℤ, IsGobelASequence 5 0 a ∧
    a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 1 ∧ a 5 = 0 := by
  obtain ⟨a, ha, -⟩ :=
    existsUnique_gobelASequence 5 0 (by decide) (by decide) ⟨0, rfl⟩ (by decide)
  have h2 : a 1 = a 2 := ha.2.2.2.2.2 1 (by decide) (by decide)
  have h3 : a 2 = a 3 := ha.2.2.2.2.2 2 (by decide) (by decide)
  have h4 : a 3 = a 4 := ha.2.2.2.2.2 3 (by decide) (by decide)
  have h1 : a 1 = 1 := ha.2.2.1
  refine ⟨a, ha, h1, h2 ▸ h1, h3 ▸ h2 ▸ h1, h4 ▸ h3 ▸ h2 ▸ h1, ha.2.1 5 (Or.inr le_rfl)⟩

end MathlibExtTest.NumberTheory.GobelNonIntegralityExistsUniqueGobelASequence
