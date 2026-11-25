/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SquarefulTwoPowOmega

/-! # Specializations of the coarse squareful zeta factorization -/

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
