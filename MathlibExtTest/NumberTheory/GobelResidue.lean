/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Defs.LinearOrder
import MathlibExt.NumberTheory.GobelResidue

namespace MathlibExtTest.NumberTheory.GobelResidue

open MetaMathlibExt

-- For k = 2, p = 3, r = 1 and n = 2, the residue is `some 0`, so `g_{2,2}(2)` is 3-integral.
theorem gobelSequence_two_two_two_padic_nonneg :
    0 ≤ padicValRat 3 (gobelSequence 2 2 2) := by
  have hp : Nat.Prime 3 := by decide
  have hnr : padicValNat 3 (2).factorial ≤ 1 := by decide +kernel
  have hR : gobelResidue 2 3 1 2 = some 0 := by decide +kernel
  have hR_ne : gobelResidue 2 3 1 2 ≠ none := by rw [hR]; exact Option.some_ne_none 0
  have hiff := gobelResidue_eq_none_iff 2 3 1 2 (by decide) (by decide) hp (by decide) hnr
  have hnot_neg : ¬ padicValRat 3 (gobelSequence 2 2 2) < 0 := mt hiff.mpr hR_ne
  exact le_of_not_gt hnot_neg

end MathlibExtTest.NumberTheory.GobelResidue
