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
