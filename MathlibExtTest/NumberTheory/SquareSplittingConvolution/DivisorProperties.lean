/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties

open MetaMathlibExt

-- Zero and one are coprime, and the convention for zero gives the singleton {1}.
example : squareSplitDivisors (0 * 1) = {1} := by
  rw [squareSplitDivisors_properties.2.1 0 1 (by decide), squareSplitDivisors_one]
  decide +kernel

-- At 8 the two splitting factors share the prime 2, but all four choices are distinct.
example : (squareSplitDivisors 8).card = 4 := by
  rw [(squareSplitDivisors_properties.2.2 8 (by decide)).2]
  decide +kernel

-- At a prime square the prime itself is absent, although both endpoints occur.
example : 1 ∈ squareSplitDivisors 25 ∧ 25 ∈ squareSplitDivisors 25 ∧
    5 ∉ squareSplitDivisors 25 := by
  obtain ⟨h₁, h₂₅, _⟩ := squareSplitDivisors_properties.1 25 (by decide)
  exact ⟨h₁, h₂₅, by decide +kernel⟩
