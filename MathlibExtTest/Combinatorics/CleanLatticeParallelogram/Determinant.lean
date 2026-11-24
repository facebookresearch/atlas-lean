/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CleanLatticeParallelogram.Determinant

/-! # Tests for the signed determinant of three convergent vectors -/

open MetaMathlibExt

namespace MetaMathlibExt.convergentVec_det_three

-- The continued fraction 157/68 = [2; 3, 4, 5] has two triples of alternate vectors.
private theorem terminalIndex :
    IsLeast {k | (GenContFract.of ((157 : ℚ) / 68)).TerminatedAt k} 3 := by
  constructor
  · change (GenContFract.of ((157 : ℚ) / 68)).s.get? 3 = none
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  · intro k hk
    by_contra! h
    have : ((GenContFract.of ((157 : ℚ) / 68)).s.get? 2).isSome := by decide +kernel
    exact Option.isSome_iff_ne_none.mp this (GenContFract.terminated_stable (by omega : k ≤ 2) hk)

-- At i = 0 the first row uses the initial vector with index -2.
example :
    let v := convergentVec ((157 : ℚ) / 68)
    Matrix.det !![1, (v (-2)).1, (v (-2)).2;
        1, (v 0).1, (v 0).2; 1, (v 2).1, (v 2).2] = -24 := by
  apply (convergentVec_det_three (i := 0) (by decide) (by decide) terminalIndex (by decide)).trans
  have h : (partialQuotient ((157 : ℚ) / 68) 0 * partialQuotient ((157 : ℚ) / 68) 1 *
      partialQuotient ((157 : ℚ) / 68) 2) = 24 := by decide +kernel
  norm_num [h]

-- At i = 1 the last row reaches the terminal vector and the sign is positive.
example :
    let v := convergentVec ((157 : ℚ) / 68)
    Matrix.det !![1, (v (-1)).1, (v (-1)).2;
        1, (v 1).1, (v 1).2; 1, (v 3).1, (v 3).2] = 60 := by
  apply (convergentVec_det_three (i := 1) (by decide) (by decide) terminalIndex (by decide)).trans
  have h : (partialQuotient ((157 : ℚ) / 68) 1 * partialQuotient ((157 : ℚ) / 68) 2 *
      partialQuotient ((157 : ℚ) / 68) 3) = 60 := by decide +kernel
  norm_num [h]

end MetaMathlibExt.convergentVec_det_three
