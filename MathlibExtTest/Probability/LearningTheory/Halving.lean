/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.Halving

@[expose] public section

/-- Boundary check: with two concepts and no examples, the
halving bound `2 ^ 0 ≤ 2` instantiates. -/
example (c₁ c₂ : Bool → Bool) :
    2 ^ halvingMistakes {c₁, c₂} [] ([] : List (Bool × Bool)) ≤
      ({c₁, c₂} : Finset (Bool → Bool)).card := by
  have h := halving_mistakes_bound {c₁, c₂} ([] : List (Bool × Bool))
    ⟨c₁, by simp, by simp⟩
  simpa using h
