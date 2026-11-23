/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedHofstadterOrder

/-!
# Tests for generalized Hofstadter prefix counts
-/

open MetaMathlibExt

example (k : ℕ) : hofCount k (· = 1) 0 = 0 := rfl

-- The one-letter alphabet gives a prefix consisting entirely of ones.
example : hofPrefix 1 5 = [1, 1, 1, 1, 1] ∧ hofCount 1 (· = 1) 5 = 5 := by decide

-- Extending the prefixes can turn a strict inequality into equality.
example : hofCount 3 (· = 1) 5 = 1 ∧ hofCount 2 (· = 1) 5 = 2 := by decide

example : hofCount 3 (· = 1) 8 = 3 ∧ hofCount 2 (· = 1) 8 = 3 := by decide

example (n : ℕ) : hofCount 3 (· = 1) n ≤ hofCount 2 (· = 1) n :=
  hofCount_one_succ_le (by decide : 1 ≤ 2) n
