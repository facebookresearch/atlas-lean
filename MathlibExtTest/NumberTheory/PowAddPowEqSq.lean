/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PowAddPowEqSq

namespace MetaMathlibExt

/-- `2^3 + 1 = 3^2`. -/
example : 2 ^ 3 + 1 = 3 ^ 2 := (two_pow_add_one_eq_sq 3 3).2 ⟨rfl, rfl⟩

/-- `2^5 + 1 = 33` is not a square. -/
example (z : ℕ) : 2 ^ 5 + 1 ≠ z ^ 2 := fun h =>
  absurd ((two_pow_add_one_eq_sq 5 z).1 h).1 (by decide)

#print axioms two_pow_add_one_eq_sq

end MetaMathlibExt
