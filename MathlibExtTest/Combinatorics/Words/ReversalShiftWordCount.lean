/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OEIS/108081.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.Combinatorics.Words.ReversalShiftWordCount

@[expose] public section

/-!
# Tests for `MathlibExt.Combinatorics.Words.ReversalShiftWordCount`

The term tests are the ones carried by `FormalConjectures/OEIS/108081.lean`, which checks
the first values of `a` against the official OEIS b-file.
-/

namespace MathlibExtTest.Combinatorics.Words.ReversalShiftWordCount

open OeisA108081

-- Source faithfulness: the Formal Conjectures statement
-- `OeisA108081.count_words_in_x_is_a_shifted`, verbatim.
example (n : ℕ) : n ≥ 1 → Set.ncard (xN n) = a (n - 1) :=
  count_words_in_x_is_a_shifted n

example : a 0 = 1 := by decide
example : a 1 = 2 := by decide
example : a 2 = 7 := by decide
example : a 3 = 25 := by decide
example : a 4 = 92 := by decide

-- The one-letter word `[0]` is in `X`, so `|X_1| = a 0 = 1` is not vacuous.
example : [(0 : ℤ)] ∈ xN 1 := ⟨XWord.base, rfl⟩

example : Set.ncard (xN 1) = 1 := by
  rw [count_words_in_x_is_a_shifted 1 (by norm_num)]
  decide

end MathlibExtTest.Combinatorics.Words.ReversalShiftWordCount
