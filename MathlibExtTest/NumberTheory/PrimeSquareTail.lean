/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeSquareTail
import Mathlib.Analysis.PSeries

/-!
# Tests for the reciprocal prime-square tail
-/

open Asymptotics Filter MetaMathlibExt

-- The logarithmic factor gives decay strictly faster than the reciprocal cutoff.
example :
    (fun n : ℕ ↦ ∑' p : {p : ℕ // p.Prime ∧ n < p}, 1 / ((p : ℕ) : ℝ) ^ 2)
      =o[atTop] (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
  apply tsum_inv_sq_primes_gt_isBigO.trans_isLittleO
  have h : (fun n : ℕ ↦ (Real.log n)⁻¹) =o[atTop] (fun _ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      |>.inv_tendsto_atTop)
  simpa [one_div, mul_comm] using (isBigO_refl (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop).mul_isLittleO h

-- At cutoff 2 the series converges and contains the contribution from 3.
example : (1 : ℝ) / 9 ≤ ∑' p : {p : ℕ // p.Prime ∧ 2 < p}, 1 / ((p : ℕ) : ℝ) ^ 2 := by
  have h : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} ↦ 1 / ((p : ℕ) : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).subtype _
  have h₃ := h.le_tsum ⟨3, by decide, by decide⟩ (fun _ _ ↦ by positivity)
  norm_num at h₃ ⊢
  exact h₃
