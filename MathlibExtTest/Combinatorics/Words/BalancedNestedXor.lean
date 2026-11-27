/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.BalancedNestedXor

namespace MetaMathlibExt.balanced_nested_xor

private def alternating (n : ℕ) : Bool := n % 2 == 0

-- For the alternating sequence starting with true, the selectors give opposite bits.
example (n : ℕ) :
    alternating (2 * n + (alternating n).toNat) = !alternating n ∧
      alternating (2 * n + 1 - (alternating n).toNat) = alternating n := by
  have he (k : ℕ) : alternating (2 * k) = true := by simp [alternating]
  have ho (k : ℕ) : alternating (2 * k + 1) = false := by simp [alternating, Nat.add_mod]
  simpa only [he, ho, Bool.true_xor, Bool.false_xor] using
    balanced_nested_xor alternating (fun k => by simp [he, ho]) n

end MetaMathlibExt.balanced_nested_xor
