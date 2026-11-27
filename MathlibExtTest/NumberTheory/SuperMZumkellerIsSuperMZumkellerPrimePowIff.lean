/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerPrimePowIff

/-! # Tests for super-m-Zumkeller prime powers

Concrete instances of `isSuperMZumkeller_prime_pow_iff`: `4 = 2 ^ 2` is super-m-Zumkeller
while `3 = 3 ^ 1` is not.
-/

namespace MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerPrimePowIff

open MathlibExt.NumberTheory.SuperMZumkellerWanted

-- `4 = 2 ^ 2` is super-m-Zumkeller since `2 % 16 = 2`.
example : IsSuperMZumkeller (2 ^ 2) :=
  (isSuperMZumkeller_prime_pow_iff 2 Nat.prime_two 2 (by decide)).mpr (by decide)

-- `3 = 3 ^ 1` is not super-m-Zumkeller since `1 % 16 = 1`.
example : ¬ IsSuperMZumkeller (3 ^ 1) := by
  intro h
  have hmem := (isSuperMZumkeller_prime_pow_iff 3 Nat.prime_three 1 (by decide)).mp h
  exact absurd hmem (by decide)

end MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerPrimePowIff
