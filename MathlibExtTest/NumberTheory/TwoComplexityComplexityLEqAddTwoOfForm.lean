/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexityComplexityLEqAddTwoOfForm

/-!
# Tests for the four forms with 2-complexity `m + 2`

Concrete instances cover the four forms, including coincident exponents in the third form.
-/

namespace MathlibExtTest.NumberTheory.TwoComplexityComplexityLEqAddTwoOfForm

open MathlibExt.NumberTheory.TwoComplexityWanted

example : complexityL 2 14 = 5 := by
  apply complexityL_eq_add_two_of_form 3 14 (by decide) (by decide) (by decide) (by decide)
  exact Or.inl ⟨2, 1, by decide⟩

example : complexityL 2 60 = 7 := by
  apply complexityL_eq_add_two_of_form 5 60 (by decide) (by decide) (by decide) (by decide)
  exact Or.inr (Or.inl ⟨4, 3, 2, by decide⟩)

example : complexityL 2 84 = 8 := by
  apply complexityL_eq_add_two_of_form 6 84 (by decide) (by decide) (by decide) (by decide)
  exact Or.inr (Or.inr (Or.inl ⟨3, by decide⟩))

example : complexityL 2 1080 = 12 := by
  apply complexityL_eq_add_two_of_form 10 1080 (by decide) (by decide) (by decide) (by decide)
  exact Or.inr (Or.inr (Or.inr (by decide)))

end MathlibExtTest.NumberTheory.TwoComplexityComplexityLEqAddTwoOfForm
