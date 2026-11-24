/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import MathlibExt.Combinatorics.Additive.ConsecutiveOrthogonal

namespace MetaMathlibExt

/-- A row of two ones forces the block to contain both coordinates. -/
example : ∃ s t : Fin 2, s < t ∧ ∑ _j ∈ Finset.Icc s t, (1 : ZMod 2) = 0 := by
  obtain ⟨s, t, hst, hsum⟩ := exists_consecutive_orthogonal (a := 1) (m := 2)
    (by decide) (fun _ _ => 1)
  refine ⟨s, t, hst.lt_of_ne ?_, hsum 0⟩
  rintro rfl
  simpa using hsum 0

/-- One column below the bound, two alternating rows can have no common zero-sum block. -/
example : ¬ ∃ s t : Fin 3, s ≤ t ∧ ∀ i : Fin 2,
    ∑ j ∈ Finset.Icc s t, (if j.val % 2 = i.val then (1 : ZMod 2) else 0) = 0 := by
  decide

/-- With no rows, the theorem still gives a nonzero vector in dimension one. -/
example : ∃ w : Fin 1 → ZMod 2, w ≠ 0 :=
  (exists_ne_zero_orthogonal (a := 0) (m := 1) (by decide) Fin.elim0).imp fun _ hw => hw.1

/-- For the row `(1, 1)`, the nonzero witness has coordinate sum zero. -/
example : ∃ w : Fin 2 → ZMod 2, w ≠ 0 ∧ w 0 + w 1 = 0 := by
  obtain ⟨w, hw, hrow⟩ := exists_ne_zero_orthogonal (a := 1) (m := 2)
    (by decide) (fun _ _ => 1)
  exact ⟨w, hw, by simpa only [Fin.sum_univ_two, mul_one] using hrow 0⟩

end MetaMathlibExt
