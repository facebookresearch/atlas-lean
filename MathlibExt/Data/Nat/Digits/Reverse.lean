/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs

@[expose] public section

namespace Nat

/-- **Digit reversal.** For natural numbers $b$ and $n$ with $b \ge 2$, write
$n = \sum_{i<k} d_i b^i$ with digits $0 \le d_i < b$ and leading digit $d_{k-1} \ne 0$ (so $k = 0$
when $n = 0$). The base-$b$ reversal of $n$ is the natural number $\sum_{i<k} d_{k-1-i} b^i$. For
the bases $b = 0$ and $b = 1$ the reversal of $n$ is $n$ itself.

Trailing zeros of $n$ become leading zeros and are lost: in base $10$ the reversal of $120$ is
$21$. -/
def reverseDigits (b n : ℕ) : ℕ :=
  Nat.ofDigits b (Nat.digits b n).reverse

@[simp] theorem reverseDigits_base_zero (n : ℕ) : reverseDigits 0 n = n := by
  cases n <;> simp [reverseDigits]

@[simp] theorem reverseDigits_base_one (n : ℕ) : reverseDigits 1 n = n := by
  simp [reverseDigits, Nat.ofDigits_one]

end Nat
