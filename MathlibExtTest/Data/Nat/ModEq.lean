/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Nat.ModEq

-- Inversion by two works for a nonzero residue modulo an odd modulus.
example : 2 * 4 ≡ 3 [MOD 5] ∧ 4 ≡ ((5 + 1) / 2) * 3 [MOD 5] := by decide

example : 4 ≡ ((5 + 1) / 2) * 3 [MOD 5] :=
  (Nat.two_mul_modEq_iff_of_odd (by decide : Odd 5) 4 3).mp (by decide)
