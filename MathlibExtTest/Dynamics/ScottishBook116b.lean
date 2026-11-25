/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.ScottishBook116b

/-! # Tests for the measurable-set form of Scottish Book Problem 116(b) -/

open MathlibExt.Dynamics.ScottishBook116bWanted

universe u

example : ¬ ScottishBookProblem116bClaim.{u} := scottishBook116b_refuted

example : MeasureTheory.IsProbabilityMeasure coinFlip := inferInstance

example {G : Type u} [Group G] (φ ψ : G) (c : ℕ → Bool)
    (h₀ : c 0 = false) (h₁ : c 1 = true) :
    partialProd φ ψ c 2 = φ * ψ := by
  simp [partialProd, step, h₀, h₁]
