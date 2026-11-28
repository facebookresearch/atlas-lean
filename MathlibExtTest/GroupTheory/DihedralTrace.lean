/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.DihedralTrace

import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic

-- The hypotheses hold for `G = H = ℤˣ` acting on `ℤ` by multiplication, `τ = -1`, `y = 1`,
-- `σ' = 1`, `ε = -1` and `t = 0`: then `τ y = -y = ε σ' y + 0`.
open scoped Classical in
example : (-1 : ℤˣ) • ∑ h : (⊤ : Subgroup ℤˣ), ((h : ℤˣ) • (1 : ℤ)) =
      ((-1 : ℤˣ) : ℤ) • ∑ h : (⊤ : Subgroup ℤˣ), ((h : ℤˣ) • (1 : ℤ)) +
        ∑ h : (⊤ : Subgroup ℤˣ), ((h : ℤˣ)⁻¹ • (0 : ℤ)) ∧
    IsOfFinAddOrder (∑ h : (⊤ : Subgroup ℤˣ), ((h : ℤˣ)⁻¹ • (0 : ℤ))) :=
  DistribMulAction.smul_sum_smul_eq_of_mul_eq_inv_mul (⊤ : Subgroup ℤˣ) (τ := -1)
    (fun h _ => by rw [Int.units_inv_eq_self, mul_comm]) (Subgroup.mem_top 1) (-1)
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨1, one_pos, by simp⟩) (by simp [Units.smul_def])
