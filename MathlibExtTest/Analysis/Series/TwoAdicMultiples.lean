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

-- At cutoff zero all positive indices occur, including for a nonsummable family.
example (c : ℕ → ℂ) (hc : ¬ Summable (fun p : ℕ => c (p + 1))) :
    ∑' x : ℕ × ℕ, c ((2 * x.2 + 1) * 2 ^ x.1) = 0 := by
  simpa using (tsum_twoAdic_high_regroup 0 c).trans (by simpa using tsum_eq_zero_of_not_summable hc)

-- With cutoff two, a sequence supported on [0, 4] contributes exactly its value at four.
example (c : ℕ → ℂ) (hc : ∀ n > 4, c n = 0) :
    ∑' x : ℕ × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 + 2)) = c 4 := by
  rw [tsum_twoAdic_high_regroup]
  apply tsum_eq_single 0
  intro p hp
  exact hc _ (by omega)

end MetaMathlibExt.tsum_twoAdic_high_regroup
