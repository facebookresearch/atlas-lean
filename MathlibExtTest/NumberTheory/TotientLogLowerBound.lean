/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TotientLogLowerBound

/-!
# Tests: the elementary totient lower bound
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.TotientLogLowerBound

set_option autoImplicit false

#print axioms Nat.totient_mul_one_add_log_ge

/-- At `r = 1` both sides are `1`. -/
theorem totient_bound_one : (1 : ℝ) ≤ (1 + Nat.log 2 1) * Nat.totient 1 := by
  have hNat : (1 : ℕ) ≤ (1 + Nat.log 2 1) * Nat.totient 1 := by decide
  exact_mod_cast hNat

/-- At `r = 6`: `φ(6) = 2` and `log₂ 6 = 2`, so `6 ≤ 3 * 2` with equality. -/
theorem totient_bound_six : (6 : ℝ) ≤ (1 + Nat.log 2 6) * Nat.totient 6 := by
  have hNat : (6 : ℕ) ≤ (1 + Nat.log 2 6) * Nat.totient 6 := by decide
  exact_mod_cast hNat

/-- At `r = 12`: `φ(12) = 4` and `log₂ 12 = 3`, so `12 ≤ 4 * 4`. -/
theorem totient_bound_twelve : (12 : ℝ) ≤ (1 + Nat.log 2 12) * Nat.totient 12 := by
  have hNat : (12 : ℕ) ≤ (1 + Nat.log 2 12) * Nat.totient 12 := by decide
  exact_mod_cast hNat

/-- The bound is not vacuous at a prime power: `φ(8) = 4`, `log₂ 8 = 3`. -/
theorem totient_bound_eight : (8 : ℝ) ≤ (1 + Nat.log 2 8) * Nat.totient 8 := by
  have hNat : (8 : ℕ) ≤ (1 + Nat.log 2 8) * Nat.totient 8 := by decide
  exact_mod_cast hNat

end MathlibExtTest.NumberTheory.TotientLogLowerBound
