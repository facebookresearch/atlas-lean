/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GolombRulers

open Finset MathlibExt.Combinatorics.GolombRulersWanted

example : optimalGolombLength 11 = 72 :=
  congrArg (fun lengths : List ℕ => lengths[8]!) optimalGolombLength_three_to_eleven

example : optimalGolombLength 0 = 0 := rfl

-- The definition permits a ruler whose first mark is positive.
example : 5 ∈ golombRulerLengths 3 := by
  let S : Finset ℕ := {2, 3, 5}
  have hsub : S ⊆ range 6 := by decide +revert
  have hs : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by decide +revert
  exact ⟨S, hsub, by decide +revert, hs, by decide +revert⟩
