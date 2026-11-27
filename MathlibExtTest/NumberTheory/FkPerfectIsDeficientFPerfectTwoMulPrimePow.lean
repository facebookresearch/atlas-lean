/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectIsDeficientFPerfectTwoMulPrimePow
namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

-- Six is deficient `F`-perfect, from the `p = 3`, `a = 1` instance.
example : IsDeficientFPerfect 6 :=
  (isDeficientFPerfect_two_mul_prime_pow 3 1 (by decide)).1

-- Ten is `2 * 5 ^ 1` but not `6`, so it is not deficient `F`-perfect.
example : ¬ IsDeficientFPerfect (2 * 5 ^ 1) := by
  intro h
  have h6 := (isDeficientFPerfect_two_mul_prime_pow 5 1 (by decide)).2 h
  exact absurd h6 (by decide)

-- The divisor `d = 2` witnesses `6` through the `p = 3`, `a = 1` instance.
example : 2 * 3 ^ 1 = 6 :=
  (isDeficientFPerfect_two_mul_prime_pow 3 1 (by decide)).2
    ⟨2, by decide, by decide, by decide⟩

end MathlibExtTest.NumberTheory.FkPerfect
