/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BloomFilterFalsePositive.UpperBound

/-!
# Tests for the elementary upper bound on the Bloom-filter false-positive rate

Small concrete instances of the upper bound and the degenerate cases, plus a two-sided
bound chaining the classical lower bound with the new upper bound.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.BloomFilter.UpperBoundTest

open Cslib.Algorithms.Lean.BloomFilter

example : falsePositiveProb 2 1 2 ≤ 1 - (1 - 1 / (2 : ℝ)) ^ (1 * 2) :=
  falsePositiveProb_le (by norm_num) (by norm_num)

example : falsePositiveProb 2 1 2 ≤ 3 / 4 := by
  have h := falsePositiveProb_le (m := 2) (n := 1) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : falsePositiveProb 2 0 2 = 0 :=
  falsePositiveProb_zero_stored (by norm_num) (by norm_num)

example : falsePositiveProb 2 1 0 = 1 :=
  falsePositiveProb_zero_hashes

example : (1 - (1 - 1 / (2 : ℝ)) ^ (1 * 2)) ^ 2 ≤ falsePositiveProb 2 1 2 ∧
    falsePositiveProb 2 1 2 ≤ 1 - (1 - 1 / (2 : ℝ)) ^ (1 * 2) :=
  ⟨classical_le_falsePositiveProb (by norm_num), falsePositiveProb_le (by norm_num) (by norm_num)⟩

end Cslib.Algorithms.Lean.BloomFilter.UpperBoundTest
