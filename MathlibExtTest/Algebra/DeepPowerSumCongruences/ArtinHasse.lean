/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.ArtinHasse

open MetaMathlibExt PowerSeries

-- At N = 0 the divisor product is empty and the truncation is 1.
example (p : ℕ) [Fact p.Prime] :
    trunc (0 + 1) ((exp ℚ).subst (mk fun m : ℕ =>
      if p ^ Nat.log p m = m then (m : ℚ)⁻¹ else 0) : PowerSeries ℚ) = 1 := by
  simpa only [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1),
    Finset.filter_empty, Finset.prod_empty, trunc_one] using artinHasse_eq_prod_one_sub_pow p 0

-- For p = 2 and N = 3, the even index is excluded and the two remaining factors
-- have opposite signs in their logarithms.
example :
    trunc (3 + 1) ((exp ℚ).subst (mk fun m : ℕ =>
      if 2 ^ Nat.log 2 m = m then (m : ℚ)⁻¹ else 0) : PowerSeries ℚ) =
    trunc (3 + 1) (((exp ℚ).subst (mk fun m : ℕ => if m ≠ 0 then (m : ℚ)⁻¹ else 0) :
      PowerSeries ℚ) * ((exp ℚ).subst (mk fun m : ℕ =>
        if m ≠ 0 ∧ 3 ∣ m then -(m : ℚ)⁻¹ else 0) : PowerSeries ℚ)) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h : (Finset.Icc 1 3).filter (fun d : ℕ => ¬ 2 ∣ d) = {1, 3} := by decide
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  rw [artinHasse_eq_prod_one_sub_pow 2 3, h, Finset.prod_insert (by decide), Finset.prod_singleton]
  simp [h3, div_eq_mul_inv]
