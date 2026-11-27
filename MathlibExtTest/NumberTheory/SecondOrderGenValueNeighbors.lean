/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SecondOrderGenValueNeighbors
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- At 1/3 the modulus is 5. At both neighbours it is -5.
example : secondOrderGenValue 1 3 1 (1 / 3) = 3 ∧
    secondOrderGenValue 1 3 1 (3 / 4) = -8 ∧ secondOrderGenValue 1 3 1 2 = -1 := by
  norm_num [secondOrderGenValue]

-- With p = -1 the forward denominator can be negative while the backward numerator is zero.
example (a b : ℤ) : (∃ z : ℤ, secondOrderGenValue a b (-1) (-(1 / 2)) = z) ∧
    ∃ z : ℤ, secondOrderGenValue a b (-1) 0 = z := by
  have h := secondOrderGenValue_neighbors_integer a b (-1) (by decide) (-1) 1
    (by decide) (by decide) (by decide) (by decide) ⟨b, by simp [secondOrderGenValue]⟩
  norm_num at h ⊢
  exact h

end MetaMathlibExt
