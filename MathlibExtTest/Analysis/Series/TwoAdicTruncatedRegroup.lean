/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.TwoAdicTruncatedRegroup

/-!
# Tests for truncated two-adic regrouping
-/

namespace MetaMathlibExt.tsum_twoAdic_truncated_regroup

-- At cutoff two, an atom at 24 has quotient 6 and receives the weight at 2 + 1.
example (φ : ℕ → ℂ) :
    ∑' x : ℕ × ℕ, φ (x.1 + 2) * (if (2 * x.2 + 1) * 2 ^ (x.1 + 2) = 24 then 1 else 0)
      = φ 3 := by
  rw [tsum_twoAdic_truncated_regroup 2 φ (fun m => if m = 24 then 1 else 0)]
  have h (p : ℕ) : (p + 1) * 2 ^ 2 = 24 ↔ p = 5 := by omega
  simp_rw [h, mul_ite, mul_one, mul_zero]
  rw [tsum_ite_eq, show padicValNat 2 (5 + 1) = 1 by decide +kernel]

-- The zero cutoff also applies when the weighted family is nonsummable.
example (φ c : ℕ → ℂ)
    (h : ¬ Summable (fun p : ℕ => φ (padicValNat 2 (p + 1)) * c (p + 1))) :
    ∑' x : ℕ × ℕ, φ x.1 * c ((2 * x.2 + 1) * 2 ^ x.1) = 0 := by
  simpa using (tsum_twoAdic_truncated_regroup 0 φ c).trans
    (by simpa using tsum_eq_zero_of_not_summable h)

end MetaMathlibExt.tsum_twoAdic_truncated_regroup
