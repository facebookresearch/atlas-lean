/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RadicalCoefficientCommonPrime
import Mathlib.Data.Rat.Sqrt
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic.LinearCombination

/-!
# Tests for common prime divisors of the radical norm and coefficient gcd
-/

namespace MetaMathlibExt.RadicalCoefficientCommonPrimeTest

open Polynomial

/-- Integer coordinates of `(1 + √3)^m`, in the basis `1, √3`. -/
private def coords : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((coords m).1 + 3 * (coords m).2, (coords m).1 + (coords m).2)

-- At the boundary `N = 2`, the norm is `-2` and `D₂ = gcd(4, 2) = 2`.
example : (2 : ℕ) ∣ 2 := by
  have hirr : Irreducible (X ^ 2 - C (3 : ℚ)) := by
    apply irreducible_X_pow_sub_C_of_prime Nat.prime_two
    have hns : ¬ IsSquare (3 : ℚ) := by decide +kernel
    intro q hq
    exact hns ⟨q, by simpa only [pow_two] using hq.symm⟩
  have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hexp (m : ℕ) : (1 + Real.sqrt 3) ^ m =
      (coords m).1 + (coords m).2 * Real.sqrt 3 := by
    induction m with
    | zero => simp [coords]
    | succ m ih =>
      rw [pow_succ, ih, coords]
      push_cast
      linear_combination ((coords m).2 : ℝ) * hsq
  let a : ℕ → Fin 2 → ℤ := fun m i ↦ if i = 0 then (coords m).1 else (coords m).2
  refine prime_dvd_gcd_pow_add_radical_coeffs (N := 2) (u := 1) (v := 3) (by decide)
    (by decide) (by simpa using hirr) a ?_ 2 (by decide) 2 Nat.prime_two ?_
  · intro m _
    simpa [a, Fin.sum_univ_succ, Real.sqrt_eq_rpow] using hexp m
  · refine (dvd_gcd_iff ..).2 ⟨by decide, Finset.dvd_gcd ?_⟩
    intro i _
    fin_cases i <;> decide

end MetaMathlibExt.RadicalCoefficientCommonPrimeTest
