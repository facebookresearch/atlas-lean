/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.RelativePositionInjective

/-! # Tests for the relative position function determining a binary word -/

namespace MetaMathlibExt.eq_iff_relativePosition_eq

private def ab (i : ℕ) : Bool := decide (i % 2 = 0)

-- The only word with both letters infinitely often and relative positions all one is abab….
example {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (h : ∀ n, 1 ≤ n → relativePosition w n = 1) : w = ab := by
  have hab : BothLettersInfinite ab := by
    constructor <;> apply Set.infinite_of_forall_exists_gt <;> intro n
    · exact ⟨2 * (n + 1), by simp [ab], by omega⟩
    · exact ⟨2 * (n + 1) + 1, by simp [ab, Nat.add_mod], by omega⟩
  refine (eq_iff_relativePosition_eq hw hab).2 fun n hn => ?_
  rw [h n hn, relativePosition_of_dimers (fun i => by simp [ab, Nat.add_mod]) n hn]
  simp [ab]

-- Two words made of ab and ba blocks are equal once they agree at the even positions.
example {w w' : ℕ → Bool} (hw : BothLettersInfinite w) (hw' : BothLettersInfinite w')
    (hdim : ∀ i, w (2 * i) ≠ w (2 * i + 1)) (hdim' : ∀ i, w' (2 * i) ≠ w' (2 * i + 1))
    (heven : ∀ i, w (2 * i) = w' (2 * i)) : w = w' := by
  refine (eq_iff_relativePosition_eq hw hw').2 fun n hn => ?_
  rw [relativePosition_of_dimers hdim n hn, relativePosition_of_dimers hdim' n hn, heven]

end MetaMathlibExt.eq_iff_relativePosition_eq
