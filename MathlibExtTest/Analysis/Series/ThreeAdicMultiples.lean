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
