/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.BaseAdicMultiples

/-!
# Tests for regrouping the multiples of a base
-/

namespace MetaMathlibExt.tsum_baseAdic_multiples_regroup

-- In the smallest base there is one residue, and the cofactor is odd.
example (c : ℕ → ℂ) (hc : Summable fun m : ℕ => c (2 * (m + 1))) :
    ∑' x : ℕ × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 + 1)) = ∑' m : ℕ, c (2 * (m + 1)) := by
  simpa [Fin.sum_univ_one, Nat.mul_succ] using tsum_baseAdic_multiples_regroup 2 (by decide) c hc

-- In base four, 32 has cofactor two, which shares a prime factor with the base.
example :
    (∑' x : ℕ × ℕ, ∑ i : Fin 3,
      if (4 * (x.2 + 1) - (i + 1)) * 4 ^ (x.1 + 1) = 32 then (1 : ℂ) else 0) = 1 := by
  let c (n : ℕ) : ℂ := if n = 32 then 1 else 0
  have h (m : ℕ) : 4 * (m + 1) = 32 ↔ m = 7 := by omega
  have hc : HasSum (fun m : ℕ => c (4 * (m + 1))) 1 := by
    simpa only [c, h] using hasSum_ite_eq 7 (1 : ℂ)
  exact (tsum_baseAdic_multiples_regroup 4 (by decide) c hc.summable).trans hc.tsum_eq

end MetaMathlibExt.tsum_baseAdic_multiples_regroup
