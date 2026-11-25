/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Combinatorics.BinaryChvatalSankoff

open scoped BigOperators
open MathlibExt.Combinatorics.BinaryChvatalSankoffWanted

example : normalizedExpectedLCS 0 = 0 := by simp [normalizedExpectedLCS]

-- The sixteen pairs of two-bit strings have total LCS length eighteen.
example : normalizedExpectedLCS 2 = 9 / 16 := by
  have hsum : ∑ p ∈ uniformBinaryStringPairs 2, lcsLength p.1 p.2 = 18 := by decide
  norm_num [normalizedExpectedLCS, expectedLCSLength, ← Nat.cast_sum, hsum,
    BinaryStringPair, BinaryString, Fintype.card_fun]
