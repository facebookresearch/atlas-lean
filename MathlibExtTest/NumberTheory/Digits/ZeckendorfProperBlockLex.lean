/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfProperBlockLex

namespace MetaMathlibExt

-- The first difference can occur at the positive block start, even for the zero function.
example : ∃ k, 1 ≤ k ∧ IsProperLStarBlock [2, 3, 0] (fun _ => 0) 1 k := by
  simpa using
    (descLexLT_maxLStarBlock_iff [2, 3, 0] (by decide) (by decide)
      (ε := fun _ => 0) (b := 1) (fun _ _ => rfl)).mp
        ⟨1, by decide, fun i hi => by simp [maxLStarBlock, hi]⟩

-- Only the prefix through the first smaller digit matters, not a later larger digit.
example : DescLexLT (fun i => if i = 1 then 2 else if i = 4 then 7 else 0)
    (maxLStarBlock [2, 3, 0] 1) := by
  refine (descLexLT_maxLStarBlock_iff [2, 3, 0] (by decide) (by decide)
    (fun i hi => by
      have hi0 : i = 0 := by omega
      subst i
      decide)).mpr ?_
  refine ⟨2, by decide, by decide, ?_, by decide, ?_⟩
  · intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> decide
  · intro i hi
    simp [not_le.mpr hi]

end MetaMathlibExt
