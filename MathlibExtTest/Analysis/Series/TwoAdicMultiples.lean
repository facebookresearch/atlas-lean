/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.TwoAdicMultiples

/-!
# Tests for regrouping the multiples of a power of two
-/

namespace MetaMathlibExt.tsum_twoAdic_high_regroup

-- At cutoff zero a nonsummable sequence has unconditional sum zero in the new indices.
example (c : ℕ → ℂ) (hc : ¬ Summable (fun p : ℕ => c (p + 1))) :
    ∑' x : ℕ × ℕ, c ((2 * x.2 + 1) * 2 ^ x.1) = 0 := by
  simpa using (tsum_twoAdic_high_regroup 0 c).trans
    (by simpa using tsum_eq_zero_of_not_summable hc)

-- Of the two supported indices 6 and 24, only 24 is a multiple of four.
example :
    (∑' x : ℕ × ℕ, if (2 * x.2 + 1) * 2 ^ (x.1 + 2) ∈ ({6, 24} : Finset ℕ)
      then (1 : ℂ) else 0) = 1 := by
  let c (m : ℕ) : ℂ := if m ∈ ({6, 24} : Finset ℕ) then 1 else 0
  rw [tsum_twoAdic_high_regroup 2 c]
  have h (p : ℕ) : (p + 1) * 2 ^ 2 ∈ ({6, 24} : Finset ℕ) ↔ p = 5 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Nat.reducePow]
    omega
  simp_rw [c, h]
  exact tsum_ite_eq 5 (fun _ => (1 : ℂ))

end MetaMathlibExt.tsum_twoAdic_high_regroup

namespace MetaMathlibExt

private noncomputable def dyadicEulerProduct (q : ℂ) (hq : ‖q‖ < 1) : ℂ :=
  ∏' j : ℕ, QPochhammer.qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1))
    (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))

-- The factorization includes q = 0; its value there is one.
example : dyadicEulerProduct 0 (by simp) = 1 := by
  rw [dyadicEulerProduct, tprod_qPochhammer_twoAdic_factorization 0 (by simp)]
  exact QPochhammer.qPochhammerInf_zero_left _ _

private theorem norm_halfI_lt_one : ‖Complex.I / 2‖ < 1 := by
  norm_num [norm_div]

-- At a nonreal point of the disk, none of the Euler factors vanish and the product is nonzero.
example : dyadicEulerProduct (Complex.I / 2) norm_halfI_lt_one ≠ 0 := by
  let q : ℂ := Complex.I / 2
  have hq : ‖q‖ < 1 := norm_halfI_lt_one
  change dyadicEulerProduct q hq ≠ 0
  rw [dyadicEulerProduct, tprod_qPochhammer_twoAdic_factorization q hq]
  change (∏' n : ℕ, (1 - q * q ^ n)) ≠ 0
  simp only [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (fun n => ?_) ?_
  · rw [← sub_eq_add_neg]
    apply sub_ne_zero.mpr
    intro he
    have ht : ‖q * q ^ n‖ < 1 := by
      rw [← pow_succ', norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
    exact (lt_irrefl (1 : ℝ)) (by simpa only [← he, norm_one] using ht)
  · simpa only [norm_neg, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖q‖

end MetaMathlibExt
