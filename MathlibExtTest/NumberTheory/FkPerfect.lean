/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfect

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

-- `2 = 2 ^ 1` is `[2,1]`-deficient-perfect, so the theorem recovers `ℓ = 1`.
example : (1 : ℕ) = 1 ∧ (1 = 2 ∨ (2 = 2 ∧ 1 = 1)) :=
  isKLDeficientPerfect_prime_pow_two_imp 2 1 1 Nat.prime_two
    (by simpa using isKLDeficientPerfect_two 2)

-- Every `[2,ℓ]`-deficient-perfect prime power has `ℓ = 1`.
example (p a l : ℕ) (hp : p.Prime) (h : IsKLDeficientPerfect 2 l (p ^ a)) : l = 1 :=
  (isKLDeficientPerfect_prime_pow_two_imp p a l hp h).1

end MathlibExtTest.NumberTheory.FkPerfect
