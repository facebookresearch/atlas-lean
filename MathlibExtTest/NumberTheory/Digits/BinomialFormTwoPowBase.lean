/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BinomialFormTwoPowBase

/-! # Tests for bases of binomial forms of powers of two -/

open MetaMathlibExt

-- The two digits of 4 in base 3 give the boundary case k = 1 and x = n.
example : ∃ x ≤ 2, 3 = 2 ^ x - 1 :=
  (binomialForm_two_pow_base 2 3 1 1 (by decide) (by decide) (by decide) (by decide)).1

-- The four digits of 1024 in base 7 are [2, 6, 6, 2], with a nonunit multiplier.
example : (∃ x ≤ 10, 7 = 2 ^ x - 1) ∧ ∃ i : ℕ, 2 = 2 ^ i :=
  binomialForm_two_pow_base 10 7 2 3 (by decide) (by decide) (by decide) (by decide)
