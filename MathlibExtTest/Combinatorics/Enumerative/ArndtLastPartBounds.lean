/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtLastPartBounds

open MetaMathlibExt

-- Of the three compositions of four, two end in one and all three have last part at least one.
example : (∑ j ∈ Finset.Icc 1 1, arndtLastPartCount 4 j) = 2 ∧
    (∑ j ∈ Finset.Icc 1 4, arndtLastPartCount 4 j) = 3 := by
  decide

-- With an interior cutoff, both Fibonacci subtractions contribute to the first count.
example : ((∑ j ∈ Finset.Icc 1 2, arndtLastPartCount 8 j : ℕ) : ℤ) = 15 ∧
    (∑ j ∈ Finset.Icc 2 8, arndtLastPartCount 8 j) = 11 := by
  obtain ⟨h₁, h₂⟩ := arndtLastPart_atMost_atLeast 2 8 (by decide) (by decide)
  exact ⟨h₁.trans (by decide), h₂.trans (by decide)⟩
