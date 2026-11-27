/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LargeZsigmondyPrimesHomogenizedCyclotomicPrimePowMul

/-! # Tests for homogenized cyclotomic values at prime-power multiples -/

namespace MathlibExtTest.NumberTheory.LargeZsigmondyPrimesHomogenizedCyclotomicPrimePowMul

open MetaMathlibExt

-- First identity at `p = 2`, `β = 2`, `k = 1`: `Φ₄(a, b) = a² + b²`.
example (a b : ℤ) : homogenizedCyclotomic 4 a b = a ^ 2 + b ^ 2 := by
  have h := (homogenizedCyclotomic_prime_pow_mul (p := 2) (β := 2) (k := 1)
    Nat.prime_two (by decide) (by decide) (by decide) a b).1
  simpa [homogenizedCyclotomic_two] using h

-- Second identity at `p = 2`, `β = 2`, `k = 1`, via `Φ₁(x, y) = x - y`.
example (a b : ℤ) : homogenizedCyclotomic 4 a b * (a ^ 2 - b ^ 2) = a ^ 4 - b ^ 4 := by
  have h := (homogenizedCyclotomic_prime_pow_mul (p := 2) (β := 2) (k := 1)
    Nat.prime_two (by decide) (by decide) (by decide) a b).2
  simpa [homogenizedCyclotomic_one] using h

-- First identity at `p = 2`, `β = 2`, `k = 3`: `Φ₁₂(a, b) = Φ₆(a², b²)`.
example (a b : ℤ) : homogenizedCyclotomic 12 a b =
    homogenizedCyclotomic 6 (a ^ 2) (b ^ 2) := by
  have h := (homogenizedCyclotomic_prime_pow_mul (p := 2) (β := 2) (k := 3)
    Nat.prime_two (by decide) (by decide) (by decide) a b).1
  simpa using h

-- Second identity at `p = 3`, `β = 2`, `k = 2`, via `Φ₂(x, y) = x + y`.
example (a b : ℤ) : homogenizedCyclotomic 18 a b * (a ^ 3 + b ^ 3) = a ^ 9 + b ^ 9 := by
  have h := (homogenizedCyclotomic_prime_pow_mul (p := 3) (β := 2) (k := 2)
    Nat.prime_three (by decide) (by decide) (by decide) a b).2
  simpa [homogenizedCyclotomic_two] using h

-- Numeric check of the first identity at `p = 2`, `β = 3`, `k = 1`.
example : homogenizedCyclotomic 8 3 1 = 82 := by
  have h := (homogenizedCyclotomic_prime_pow_mul (p := 2) (β := 3) (k := 1)
    Nat.prime_two (by decide) (by decide) (by decide) (3 : ℤ) 1).1
  simpa [homogenizedCyclotomic_two] using h

end MathlibExtTest.NumberTheory.LargeZsigmondyPrimesHomogenizedCyclotomicPrimePowMul
