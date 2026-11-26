/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum` -/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

open MetaMathlibExt
open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- With exponent 5 the disjunct `e = 1` is impossible, so the fifth-power bound holds.
example (n q m : ℕ) (h : EulerianForm n q 5 m) : q ^ 5 < 2 * m ^ 2 := by
  simpa using eulerianForm_exponent_eq_one_or_pow_five_lt n q 5 m h

-- Corollary: an exponent different from 1 forces the fifth-power bound.
example (n q e m : ℕ) (h : EulerianForm n q e m) (he : e ≠ 1) : q ^ 5 < 2 * m ^ 2 := by
  simpa [he] using eulerianForm_exponent_eq_one_or_pow_five_lt n q e m h

-- At `n = 6`, which is primitive non-deficient with `H(6) = 3` and least prime
-- factor `2`, any constant `C` in the bound satisfies `2 ≤ C`.
example (C : ℝ) (hC : ∀ n : ℕ, IsPrimitiveNondeficient n →
    (abundancySup n : ℝ) ≤ 2 + C / n.minFac) : 2 ≤ C := by
  have h6 : IsPrimitiveNondeficient 6 := by
    unfold IsPrimitiveNondeficient IsNondeficient
    decide +kernel
  have hHQ : abundancySup 6 = 3 := by
    unfold abundancySup
    decide +kernel
  have hHR : (abundancySup 6 : ℝ) = 3 := by exact_mod_cast hHQ
  have hmin : (6 : ℕ).minFac = 2 := by decide
  have hbound := hC 6 h6
  rw [hHR, hmin] at hbound
  norm_num at hbound
  linarith

-- At `n = 20`, the existential bound specializes to an inequality with `C / 2`.
example : ∃ C : ℝ, (abundancySup 20 : ℝ) ≤ 2 + C / 2 := by
  obtain ⟨C, hC⟩ := exists_abundancySup_le_two_add_div_minFac
  refine ⟨C, ?_⟩
  have h20 : IsPrimitiveNondeficient 20 := by
    unfold IsPrimitiveNondeficient IsNondeficient
    decide +kernel
  have hmin : (20 : ℕ).minFac = 2 := by decide
  have hbound := hC 20 h20
  rw [hmin] at hbound
  simpa using hbound

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum
