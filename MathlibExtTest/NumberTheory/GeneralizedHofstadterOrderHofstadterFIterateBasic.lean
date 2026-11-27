/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedHofstadterOrderHofstadterFIterateBasic

/-!
# Tests for the basic properties of iterated Hofstadter functions

These examples check the collision at `1` and `2` and surjectivity of a positive iterate.
-/

namespace MathlibExtTest.NumberTheory.GeneralizedHofstadterOrderHofstadterFIterateBasic

open MetaMathlibExt

example : (hofstadterF 2)^[3] 1 = (hofstadterF 2)^[3] 2 := by
  obtain ⟨h₁, h₂, _, _, _, _, _, _, _⟩ :=
    hofstadterF_iterate_basic (by decide : 1 ≤ 3) (by decide : 1 ≤ 2)
  exact h₁.trans h₂.symm

example (n : ℕ) : ∃ m : ℕ, (hofstadterF 1)^[2] m = n := by
  obtain ⟨_, _, _, _, _, _, _, hsurj, _⟩ :=
    hofstadterF_iterate_basic (by decide : 1 ≤ 2) (by decide : 1 ≤ 1)
  exact hsurj n

end MathlibExtTest.NumberTheory.GeneralizedHofstadterOrderHofstadterFIterateBasic
