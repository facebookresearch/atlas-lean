/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GcdLucasTheoremGcdRadicalExpansionCoeffsEqOneOfCoprime
import Mathlib.Data.Rat.Sqrt
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Coprimality tests for square-root expansion coefficients

The coefficients of positive powers of `1 + √2` are coprime.
-/

namespace MathlibExtTest.NumberTheory.GcdLucasTheoremGcdRadicalExpansionCoeffsEqOneOfCoprime

example (a : ℕ → Fin 2 → ℤ)
    (ha : ∀ n, 1 ≤ n → (1 + Real.sqrt 2) ^ n = a n 0 + a n 1 * Real.sqrt 2)
    (n : ℕ) (hn : 1 ≤ n) : Finset.univ.gcd (a n) = 1 := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (2 : ℚ)) := by
    apply irreducible_X_pow_sub_C_of_prime Nat.prime_two
    have hns : ¬ IsSquare (2 : ℚ) := by decide +kernel
    intro q hq
    exact hns ⟨q, by simpa only [pow_two] using hq.symm⟩
  apply MetaMathlibExt.gcd_radical_expansion_coeffs_eq_one_of_coprime
    (N := 2) (u := 1) (v := 2) (by decide) (by decide) hirr a
    (fun m hm ↦ by simpa [Fin.sum_univ_two, Real.sqrt_eq_rpow] using ha m hm)
    ?_ n hn
  exact ⟨-1, 0, by norm_num⟩

end MathlibExtTest.NumberTheory.GcdLucasTheoremGcdRadicalExpansionCoeffsEqOneOfCoprime
