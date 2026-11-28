/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SecondOrderGenValueFamily
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- The starting ratio `1/3` has modulus `5`; propagate two steps in each direction.
example : (∃ z : ℤ, secondOrderGenValue 1 3 1
    ((secondOrderBiSeq 1 1 3 2 : ℚ) / secondOrderBiSeq 1 1 3 3) = z) ∧
    (∃ z : ℤ, secondOrderGenValue 1 3 1
      ((secondOrderBiSeq 1 1 3 (-2) : ℚ) / secondOrderBiSeq 1 1 3 (-1)) = z) := by
  have h := secondOrderGenValue_family_integer 1 3 1 (by decide) 1 3 (by decide) (by decide)
    ⟨3, by norm_num [secondOrderGenValue]⟩
  exact ⟨h 2 (by decide), h (-2) (by decide)⟩

-- Going forward from `(1, -1)`, the term at index `2` vanishes before the target ratio at `3`.
example : ∃ z : ℤ, secondOrderGenValue 2 3 1
    ((secondOrderBiSeq 1 1 (-1) 3 : ℚ) / secondOrderBiSeq 1 1 (-1) 4) = z :=
  secondOrderGenValue_family_integer 2 3 1 (by decide) 1 (-1) (by decide) (by decide)
    ⟨1, by norm_num [secondOrderGenValue]⟩ 3 (by decide)

-- Going backward from `(1, 1)`, the term at index `-1` vanishes before the target ratio at `-3`.
example : ∃ z : ℤ, secondOrderGenValue 2 3 1
    ((secondOrderBiSeq 1 1 1 (-3) : ℚ) / secondOrderBiSeq 1 1 1 (-2)) = z :=
  secondOrderGenValue_family_integer 2 3 1 (by decide) 1 1 (by decide) (by decide)
    ⟨-3, by norm_num [secondOrderGenValue]⟩ (-3) (by decide)

end MetaMathlibExt
