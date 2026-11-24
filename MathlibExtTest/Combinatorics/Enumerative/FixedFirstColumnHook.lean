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

end MetaMathlibExt.fixedFirstColumnHook_part_genFun
