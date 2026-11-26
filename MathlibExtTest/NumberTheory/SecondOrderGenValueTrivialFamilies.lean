/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SecondOrderGenValueTrivialFamilies
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- At index -3 with p = -2 the first family has consecutive terms 5 and 2.
example (a b : ℤ) : ∃ z : ℤ, secondOrderGenValue a b (-2) (5 / 2) = z := by
  have h := (secondOrderGenValue_trivial_families_integer a b (-2) (by decide)).1 (-3) (by decide)
  change ∃ z : ℤ, secondOrderGenValue a b (-2)
    ((secondOrderBwd (-2) 0 1 4 : ℚ) / secondOrderBwd (-2) 0 1 3) = z at h
  simpa [secondOrderBwd] using h

-- The noncoprime seed (-3, 0) has a zero denominator at index 0, then gives -3/6 at index 2.
example : ∃ z : ℤ, secondOrderGenValue 0 3 (-2) (-(1 / 2)) = z := by
  have h := (secondOrderGenValue_trivial_families_integer 0 3 (-2) (by decide)).2 2
    (by norm_num [secondOrderBiSeq, secondOrderFwd])
  norm_num [secondOrderBiSeq, secondOrderFwd] at h ⊢
  exact h

example : secondOrderGenValue 0 3 (-2)
    ((secondOrderBiSeq (-2) (-3) 0 2 : ℚ) / secondOrderBiSeq (-2) (-3) 0 3) = 6 := by
  norm_num [secondOrderBiSeq, secondOrderFwd, secondOrderGenValue]

-- One step from -2/3 gives the pair (3, 4).
example : IsInSecondOrderFamily 2 ⟨-2, 3, by decide, by decide⟩ (3 / 4) := by
  refine ⟨1, ?_, ?_⟩ <;> norm_num [secondOrderBiSeq, secondOrderFwd]

end MetaMathlibExt
