/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.WellKnown
import MathlibExt.Combinatorics.Enumerative.FixedFirstColumnHook

namespace MetaMathlibExt.fixedFirstColumnHook_part_genFun

open Finset PowerSeries MathlibExt

private noncomputable def series (n k : ℕ) (h : ℤ) : ℚ⟦X⟧ :=
  ∑ s ∈ range (n + 1),
    X ^ ((s : ℤ) * (k + 1) + k * (k - h)).toNat *
      (qPochFin X ((s : ℤ) + k - h - 1).toNat)⁻¹ * gaussBinom X (s + k - 1) (k - 1)

-- The empty partition contributes no fixed hook.
example : coeff 0 (series 0 1 0) = 0 := by
  rw [series, ← fixedFirstColumnHook_part_genFun _ _ _ (by decide) (by decide)]
  decide

-- A negative shift allows both (3, 1) and (1, 1, 1, 1), with different hook rows.
example : coeff 4 (series 4 1 (-1)) = 2 := by
  have inv : (1 - X : ℚ⟦X⟧)⁻¹ = mk 1 :=
    ((PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2 (mk_one_mul_one_sub_eq_one ℚ)).symm
  norm_num [series, map_sum, sum_range_succ, mul_assoc, coeff_X_pow_mul', qPochFin_succ,
    coeff_zero_eq_constantCoeff_apply, inv, map_mul]

-- The repeated parts in (2, 2, 2) give exactly one qualifying row.
private def threeTwos : Nat.Partition 6 := ⟨{2, 2, 2}, by decide, by decide⟩

example : (Icc 1 6).filter (fun r => IsFixedColumnHook threeTwos 1 r 1 ∧
    partitionRowLen threeTwos r = 2) = {2} := by
  decide

private noncomputable def hookSizeSeries (k : ℕ) (h : ℤ) : ℚ⟦X⟧ :=
  ∑ l ∈ Icc 1 k, X ^ ((k : ℤ) + l * (k - h - 1)).toNat *
    (qPochFin X ((k : ℤ) - h - 1).toNat)⁻¹ * gaussBinom X (k - 1) (l - 1)

-- The empty partition contributes nothing, even for `k = 1` and the first row.
example : coeff 0 (hookSizeSeries 1 0) = 0 := by
  rw [hookSizeSeries, ← fixedFirstColumnHook_hook_genFun (n := 0) (k := 1) (h := 0)
    (hk := by decide) (hh := by decide)]
  decide

private theorem inv_one_sub_X : (1 - X : ℚ⟦X⟧)⁻¹ = mk 1 :=
  ((PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2 (mk_one_mul_one_sub_eq_one ℚ)).symm

-- For `k = 1, h = -1` the hook must lie in the second row, not the first.
example : ((Finset.univ.filter fun p : Nat.Partition 1 =>
    ((Icc 1 1).filter fun s => IsFixedColumnHook p 1 s (-1) ∧
      partitionHookLength p s 1 = ((1 : ℕ) : ℤ)).Nonempty).card : ℚ) = 0 := by
  rw [fixedFirstColumnHook_hook_genFun (n := 1) (k := 1) (h := -1)
    (hk := by decide) (hh := by decide), ← hookSizeSeries]
  norm_num [hookSizeSeries, qPochFin_succ, inv_one_sub_X, coeff_X_pow_mul']

example : ((Finset.univ.filter fun p : Nat.Partition 2 =>
    ((Icc 1 2).filter fun s => IsFixedColumnHook p 1 s (-1) ∧
      partitionHookLength p s 1 = ((1 : ℕ) : ℤ)).Nonempty).card : ℚ) = 1 := by
  rw [fixedFirstColumnHook_hook_genFun (n := 2) (k := 1) (h := -1)
    (hk := by decide) (hh := by decide), ← hookSizeSeries]
  norm_num [hookSizeSeries, qPochFin_succ, inv_one_sub_X, coeff_X_pow_mul', coeff_mk]

-- For `k = 3, h = 1`, the second row can have any length in `[1, 3]`.
-- The middle term actually uses the nonconstant Gaussian binomial `1 + X`.
example : coeff 6 (hookSizeSeries 3 1) = 4 := by
  have hIcc : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  norm_num [hookSizeSeries, hIcc, qPochFin_succ, inv_one_sub_X, gaussBinom_succ_succ, mul_assoc,
    mul_add, coeff_X_pow_mul', coeff_mk]

-- A fixed hook from a part of size two need not be a hook of length two.
example : (Icc 1 6).filter (fun r => IsFixedColumnHook threeTwos 1 r 1 ∧
    partitionHookLength threeTwos r 1 = 2) = ∅ := by
  decide

example : (Icc 1 6).filter (fun r => IsFixedColumnHook threeTwos 1 r 1 ∧
    partitionHookLength threeTwos r 1 = 3) = {2} := by
  decide

end MetaMathlibExt.fixedFirstColumnHook_part_genFun
