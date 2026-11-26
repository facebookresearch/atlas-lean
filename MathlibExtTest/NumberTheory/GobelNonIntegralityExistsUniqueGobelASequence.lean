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

end MathlibExtTest.NumberTheory.GobelNonIntegralityExistsUniqueGobelASequence
