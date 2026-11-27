/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.ThreeAdicMultiples

/-!
# Tests for regrouping the multiples of three
-/

namespace MetaMathlibExt.tsum_threeAdic_multiples_regroup

-- The terms at 6 and 9 have different exponents and different nonzero residues.
-- Values away from multiples of three are unrestricted.
example (b : ℕ → ℂ) (hb : ∀ n, 3 ∣ n → n ≠ 6 → n ≠ 9 → b n = 0) :
    ∑' x : ℕ × ℕ, (b ((3 * x.2 + 2) * 3 ^ (x.1 + 1)) + b ((3 * x.2 + 1) * 3 ^ (x.1 + 1)))
      = b 6 + b 9 := by
  have h : HasSum (fun m : ℕ => b (3 * (m + 1))) (∑ m ∈ ({1, 2} : Finset ℕ), b (3 * (m + 1))) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      exact hb _ (dvd_mul_right _ _) (by omega) (by omega)
  rw [tsum_threeAdic_multiples_regroup b h.summable, h.tsum_eq]
  norm_num

end MetaMathlibExt.tsum_threeAdic_multiples_regroup

namespace MetaMathlibExt

private noncomputable def ternaryEulerProduct (q : ℂ) (hq : ‖q‖ < 1) : ℂ :=
  ∏' j : ℕ, (QPochhammer.qPochhammerInf (q ^ 3 ^ j) (q ^ 3 ^ (j + 1))
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
      * QPochhammer.qPochhammerInf (q ^ (2 * 3 ^ j)) (q ^ 3 ^ (j + 1))
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)))

-- The factorization includes q = 0; its value there is one.
example : ternaryEulerProduct 0 (by simp) = 1 := by
  rw [ternaryEulerProduct, tprod_qPochhammer_threeAdic_factorization 0 (by simp)]
  exact QPochhammer.qPochhammerInf_zero_left _ _

private theorem norm_negHalf_lt_one : ‖(-(1 / 2) : ℂ)‖ < 1 := by
  norm_num [norm_div]

-- At a negative point of the disk the regrouped product does not vanish.
example : ternaryEulerProduct (-(1 / 2)) norm_negHalf_lt_one ≠ 0 := by
  let q : ℂ := -(1 / 2)
  have hq : ‖q‖ < 1 := norm_negHalf_lt_one
  change ternaryEulerProduct q hq ≠ 0
  rw [ternaryEulerProduct, tprod_qPochhammer_threeAdic_factorization q hq]
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
