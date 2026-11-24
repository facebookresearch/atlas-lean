/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FixedColumnHooks

namespace MetaMathlibExt.columnHook_size_genFun_limit

open Finset PowerSeries MathlibExt

private noncomputable def normalizedSeries (m n k : ℕ) : ℚ⟦X⟧ :=
  X ^ (m - 1) * (∏ i ∈ range (n + 1), (1 - X ^ (k + i)))⁻¹ *
    ∑ l ∈ Icc 1 k, X ^ ((m - 1) * (k - l)) *
      (∏ i ∈ range (l - 1), (1 - X ^ (m + i))) *
      (qPochFin X (l - 1) * qPochFin X (k - l))⁻¹

-- The positive shift makes the constant term vanish even at the smallest allowed column.
example : ∀ᶠ k in Filter.atTop, coeff 0 (normalizedSeries 2 0 k) = 0 := by
  filter_upwards [columnHook_size_genFun_limit 2 (by decide) 0] with k hk
  exact hk.trans (by simp [coeff_zero_eq_constantCoeff_apply])

-- In column two both denominator factors contribute to the coefficient following the leading one.
example : ∀ᶠ k in Filter.atTop, coeff 2 (normalizedSeries 2 2 k) = 2 := by
  filter_upwards [columnHook_size_genFun_limit 2 (by decide) 2] with k hk
  apply hk.trans
  let D : ℚ⟦X⟧ := (1 - X) * qPochFin X 3
  norm_num only [Nat.reduceSub, pow_one, Nat.reduceAdd]
  change coeff (1 + 1) (X * D⁻¹) = 2
  rw [coeff_succ_X_mul]
  have hD : constantCoeff D = 1 := by simp [D, qPochFin, map_prod]
  have h := congrArg (coeff 1) (PowerSeries.mul_inv_cancel D (by simp [hD]))
  have hlin : coeff 1 D = -2 := by
    norm_num [D, qPochFin_succ, coeff_one_mul, coeff_X_pow, coeff_one]
  change coeff 1 (D * D⁻¹) = coeff 1 (1 : ℚ⟦X⟧) at h
  rw [coeff_one_mul, hlin, constantCoeff_inv, hD] at h
  norm_num [coeff_one] at h
  linarith

end MetaMathlibExt.columnHook_size_genFun_limit
