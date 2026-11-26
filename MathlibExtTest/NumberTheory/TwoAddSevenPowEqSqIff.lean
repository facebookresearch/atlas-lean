/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoAddSevenPowEqSqIff

open MetaMathlibExt

/-! Tests for `MetaMathlibExt.two_add_seven_pow_eq_sq_iff`. -/

-- The solution `(y, z) = (1, 3)`: `2 + 7 = 3 ^ 2`.
example : 2 + 7 ^ 1 = (3 : Nat) ^ 2 :=
  (two_add_seven_pow_eq_sq_iff 1 3).2 rfl

-- Every solution is `(1, 3)`.
example (y z : Nat) (h : 2 + 7 ^ y = z ^ 2) : y = 1 ∧ z = 3 :=
  Prod.mk.inj ((two_add_seven_pow_eq_sq_iff y z).1 h)

-- `y = 0`: `3` is not a square.
example (z : Nat) : 2 + 7 ^ 0 ≠ z ^ 2 := fun h => by
  simpa using (two_add_seven_pow_eq_sq_iff 0 z).1 h

-- An even exponent: `2 + 7 ^ 2 = 51` is not a square.
example (z : Nat) : 2 + 7 ^ 2 ≠ z ^ 2 := fun h => by
  simpa using (two_add_seven_pow_eq_sq_iff 2 z).1 h

-- An odd exponent other than `1`: `2 + 7 ^ 7 = 823545` is not a square.
example (z : Nat) : 2 + 7 ^ 7 ≠ z ^ 2 := fun h => by
  simpa using (two_add_seven_pow_eq_sq_iff 7 z).1 h

-- The square `3 ^ 2` is reached only from the exponent `1`.
example (y : Nat) (h : 2 + 7 ^ y = 3 ^ 2) : y = 1 := by
  simpa using (two_add_seven_pow_eq_sq_iff y 3).1 h

-- The Pell-type equation `z ^ 2 = 7 * w ^ 2 + 2` behind the proof has further solutions, such
-- as `(45, 17)`; the theorem rules them out because `17` is not a power of `7`.
example : (45 : Nat) ^ 2 = 7 * 17 ^ 2 + 2 := by decide
