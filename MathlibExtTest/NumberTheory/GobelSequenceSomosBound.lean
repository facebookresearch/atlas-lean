/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelSequenceSomosBound
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- At the boundary t 0 ^ 2 = 4 = l, index 3 is bounded by g_{2,4}(3) = 40 (here t 3 = 64 / 3).
example (t : ℕ → ℝ) (ht : ∀ n : ℕ, t (n + 1) = t n ^ 2 / (n + 1)) (h0 : t 0 = 2) :
    t 3 ≤ 40 := by
  have h := somosLike_le_gobelSequence 2 4 le_rfl (by norm_num) t ht (by norm_num [h0]) 3
    (by norm_num)
  have hg : gobelSequence 2 4 3 = 40 := by norm_num [gobelSequence]
  simpa [hg] using h

-- For odd k the start may be negative, without the paper's t 0 > 1: t 0 ^ 3 = -8 ≤ 2.
example (t : ℕ → ℝ) (ht : ∀ n : ℕ, t (n + 1) = t n ^ 3 / (n + 1)) (h0 : t 0 = -2) :
    t 2 ≤ 5 := by
  have h := somosLike_le_gobelSequence 3 2 (by norm_num) le_rfl t ht (by norm_num [h0]) 2
    (by norm_num)
  have hg : gobelSequence 3 2 2 = 5 := by norm_num [gobelSequence]
  simpa [hg] using h

-- For even k a negative start works too: t 0 = -1 gives t 2 ≤ g_{2,2}(2) = 3.
example (t : ℕ → ℝ) (ht : ∀ n : ℕ, t (n + 1) = t n ^ 2 / (n + 1)) (h0 : t 0 = -1) :
    t 2 ≤ 3 := by
  have h := somosLike_le_gobelSequence 2 2 le_rfl le_rfl t ht (by norm_num [h0]) 2
    (by norm_num)
  simpa [gobelSequence_two_two_small.1] using h

-- The bound starts at index 1: t 0 = 1 satisfies t 0 ^ 2 ≤ 2, yet g_{2,2}(0) = 0 < t 0.
example : ¬ ((1 : ℝ) ≤ gobelSequence 2 2 0) := by
  norm_num [gobelSequence]

end MetaMathlibExt
