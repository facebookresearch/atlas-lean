/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ShiftedLucasComposite

open MetaMathlibExt

-- The initial Fibonacci value is zero, so the shifted term is the shift itself.
example : ¬ Nat.Prime 14475 := by
  simpa using fib_add_14475_not_prime 0

-- At index 3 the shifted term is odd and has 31 as a proper divisor.
example : ¬ Nat.Prime (31 * 467) := fib_add_14475_not_prime 3
