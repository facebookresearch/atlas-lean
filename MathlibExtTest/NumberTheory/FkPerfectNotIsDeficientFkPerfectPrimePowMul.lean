/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFkPerfectPrimePowMul
open MathlibExt.NumberTheory.FkPerfectWanted

-- A concrete instance with a positive exponent.
example : ¬ IsDeficientFkPerfect 2 (3 ^ 5 * 5) :=
  not_isDeficientFkPerfect_prime_pow_mul (k := 2) (p₁ := 3) (p₂ := 5) (a := 5)
    (hk := by decide) (hp₁ := by decide) (hp₂ := by decide)
    (ho₁ := ⟨1, rfl⟩) (ho₂ := ⟨2, rfl⟩) (hne := by decide)

-- The zero exponent is included: `5 ^ 0 * 7` is the prime `7`.
example : ¬ IsDeficientFkPerfect 3 (5 ^ 0 * 7) :=
  not_isDeficientFkPerfect_prime_pow_mul (k := 3) (p₁ := 5) (p₂ := 7) (a := 0)
    (hk := by decide) (hp₁ := by decide) (hp₂ := by decide)
    (ho₁ := ⟨2, rfl⟩) (ho₂ := ⟨3, rfl⟩) (hne := by decide)

-- Specialized to `3 ^ a * 5`, the statement holds for every exponent.
example (a : ℕ) : ¬ IsDeficientFkPerfect 2 (3 ^ a * 5) :=
  not_isDeficientFkPerfect_prime_pow_mul (k := 2) (p₁ := 3) (p₂ := 5) (a := a)
    (hk := by decide) (hp₁ := by decide) (hp₂ := by decide)
    (ho₁ := ⟨1, rfl⟩) (ho₂ := ⟨2, rfl⟩) (hne := by decide)
