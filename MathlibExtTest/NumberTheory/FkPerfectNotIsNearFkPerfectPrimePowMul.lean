/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsNearFkPerfectPrimePowMul
/-! # Tests for no near `F_k`-perfect number of the form `p₁ ^ a * p₂`

Concrete instances and a corollary of `not_isNearFkPerfect_prime_pow_mul`.
-/

open MathlibExt.NumberTheory.FkPerfectWanted

namespace MathlibExtTest.NumberTheory.FkPerfect

-- A concrete instance with `k = 2`, `p₁ = 3`, `p₂ = 5` and `a = 1`.
example : ¬ IsNearFkPerfect 2 (3 ^ 1 * 5) :=
  not_isNearFkPerfect_prime_pow_mul 2 3 5 1 (by decide) (by decide) (by decide)
    (⟨1, rfl⟩ : Odd (3 : ℕ)) (⟨2, rfl⟩ : Odd (5 : ℕ)) (by decide)

-- A concrete instance with `k = 3`, `p₁ = 5`, `p₂ = 7` and `a = 2`.
example : ¬ IsNearFkPerfect 3 (5 ^ 2 * 7) :=
  not_isNearFkPerfect_prime_pow_mul 3 5 7 2 (by decide) (by decide) (by decide)
    (⟨2, rfl⟩ : Odd (5 : ℕ)) (⟨3, rfl⟩ : Odd (7 : ℕ)) (by decide)

-- Fixing the primes gives a corollary for every `k > 1` and every exponent.
example (k a : ℕ) (hk : 1 < k) : ¬ IsNearFkPerfect k (3 ^ a * 5) :=
  not_isNearFkPerfect_prime_pow_mul k 3 5 a hk (by decide) (by decide)
    (⟨1, rfl⟩ : Odd (3 : ℕ)) (⟨2, rfl⟩ : Odd (5 : ℕ)) (by decide)

end MathlibExtTest.NumberTheory.FkPerfect
