/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SquarefulTwoPowOmega

/-! # Specializations of the squareful zeta factorizations -/

open Classical in
-- The same remainder converges below the squareful half-plane and gives the value at one.
example : ∃ h : ℕ → ℂ, LSeriesSummable h (1 / 4) ∧
    LSeries (fun n => if Nat.IsKFull 2 n then
        (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) 1 =
      riemannZeta 2 ^ 2 * riemannZeta 3 ^ 2 / riemannZeta 4 * LSeries h 1 := by
  obtain ⟨h, hsum, heq⟩ :=
    MetaMathlibExt.squareful_two_pow_omega_LSeries_eq_zeta_quotient_five
  refine ⟨h, hsum _ (by norm_num), ?_⟩
  simpa using heq 1 (by norm_num)

open Classical in
-- The fine remainder converges at 1/14, and the same coefficients give the identity at 1.
example : ∃ h : ℕ → ℂ, LSeriesSummable h (1 / 14) ∧
    LSeries (fun n => if Nat.IsKFull 2 n then
        (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) 1 =
      riemannZeta 2 ^ 2 * riemannZeta 3 ^ 2 * riemannZeta 7 ^ 2 * riemannZeta 8 ^ 4 *
          riemannZeta 12 ^ 5 * riemannZeta 13 ^ 14 * riemannZeta 14 ^ 5 /
        (riemannZeta 4 * riemannZeta 5 ^ 2 * riemannZeta 6 ^ 3 * riemannZeta 10 ^ 5 *
          riemannZeta 11 ^ 6) * LSeries h 1 := by
  obtain ⟨h, hsum, heq⟩ :=
    MetaMathlibExt.squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen
  refine ⟨h, hsum _ (by norm_num), ?_⟩
  simpa using heq 1 (by norm_num)
