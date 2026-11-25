/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RegularResidues

-- A negative nonunit can be regular when its gcd is a unitary divisor.
example : ∃ x : ℤ, (-4 : ℤ) ^ 2 * x ≡ -4 [ZMOD 12] :=
  (isRegularMod_iff_gcd_sq_eq_gcd (n := 12) (by decide) (-4)).1.mpr (by decide)

-- The gcd of 6 and 12 shares a factor with its complementary divisor.
example : ¬ ∃ x : ℤ, (6 : ℤ) ^ 2 * x ≡ 6 [ZMOD 12] := by
  obtain ⟨hsol, hcop⟩ := isRegularMod_iff_gcd_sq_eq_gcd (n := 12) (by decide) 6
  exact fun h => (by decide : ¬ Nat.Coprime 6 2) (hcop.mp (hsol.mp h))

-- Modulo one every integer is regular.
example (m : ℤ) : ∃ x : ℤ, m ^ 2 * x ≡ m [ZMOD 1] :=
  (isRegularMod_iff_gcd_sq_eq_gcd (n := 1) (by decide) m).1.mpr (by simp)
