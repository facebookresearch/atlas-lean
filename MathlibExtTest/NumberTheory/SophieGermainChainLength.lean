/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SophieGermainChainLength

-- The chain starting with 3, 7, 15 attains the bound at the smallest odd prime.
example : (∃ j ≤ 2, ¬(2 ^ j * (3 + 1) - 1).Prime) ∧
    (∀ j < 2, (2 ^ j * (3 + 1) - 1).Prime) := by
  have horder : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  constructor
  · simpa only [horder] using
      MetaMathlibExt.sophieGermainChain_length_le_orderOf_two (p := 3) (by decide) (by decide)
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    all_goals decide
