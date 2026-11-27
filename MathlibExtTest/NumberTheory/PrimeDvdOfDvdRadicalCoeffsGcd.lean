/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Rat.Sqrt
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.PrimeDvdOfDvdRadicalCoeffsGcd

/-!
# Tests for prime divisors of the radical coefficient gcd
-/

namespace MetaMathlibExt.PrimeDvdOfDvdRadicalCoeffsGcdTest

open Polynomial

/-- Integer coordinates of `(1 + √5)^m` in the basis `1, √5`. -/
private def coords : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((coords m).1 + 5 * (coords m).2, (coords m).1 + (coords m).2)

-- The cutoff `N = 2` admits a nontrivial gcd: `(1 + √5)^2 = 6 + 2√5`.
example : (2 : ℕ) ∣ 2 := by
  have hirr : Irreducible (X ^ 2 - C (5 : ℚ)) := by
    apply irreducible_X_pow_sub_C_of_prime Nat.prime_two
    have hns : ¬ IsSquare (5 : ℚ) := by decide +kernel
    intro q hq
    exact hns ⟨q, by simpa only [pow_two] using hq.symm⟩
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hexp (m : ℕ) : (1 + Real.sqrt 5) ^ m =
      (coords m).1 + (coords m).2 * Real.sqrt 5 := by
    induction m with
    | zero => simp [coords]
    | succ m ih =>
      rw [pow_succ, ih, coords]
      push_cast
      linear_combination ((coords m).2 : ℝ) * hsq
  let a : ℕ → Fin 2 → ℤ := fun m i ↦ if i = 0 then (coords m).1 else (coords m).2
  refine prime_dvd_of_dvd_radical_coeffs_gcd (N := 2) (u := 1) (v := 5) (by decide)
    (by decide) (by simpa using hirr) a ?_ 2 (by decide) 2 Nat.prime_two ?_
  · intro m _
    simpa [a, Fin.sum_univ_succ, Real.sqrt_eq_rpow] using hexp m
  · apply Finset.dvd_gcd
    intro i _
    fin_cases i <;> decide

-- For a cube root, the public theorem rules out divisibility of the coefficient gcd by 2.
example {u v : ℕ} (huv : u.Coprime v)
    (hirr : Irreducible (X ^ 3 - C (v : ℚ))) (a : ℕ → Fin 3 → ℤ)
    (ha : ∀ m, 1 ≤ m → ((u : ℝ) + (v : ℝ) ^ (1 / (3 : ℝ))) ^ m =
      ∑ i : Fin 3, (a m i : ℝ) * ((v : ℝ) ^ (1 / (3 : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) : ¬ (2 : ℤ) ∣ Finset.univ.gcd (a n) := by
  intro hpd
  exact (by decide : ¬ (2 : ℕ) ∣ 3)
    (prime_dvd_of_dvd_radical_coeffs_gcd (by decide) huv hirr a ha n hn 2 Nat.prime_two hpd)

end MetaMathlibExt.PrimeDvdOfDvdRadicalCoeffsGcdTest
