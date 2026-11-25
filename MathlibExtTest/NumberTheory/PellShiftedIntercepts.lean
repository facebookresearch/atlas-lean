/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellShiftedIntercepts

namespace MetaMathlibExt.pell_shifted_intercepts_max

-- At D = 1 and a = -1 the vertical intercepts coincide.
example (b : ℤ) :
    1 + Real.sqrt (1 + (b : ℝ) ^ 2) =
      max (max |-(1 : ℝ) + Real.sqrt (1 + (b : ℝ) ^ 2)|
        |-(1 : ℝ) - Real.sqrt (1 + (b : ℝ) ^ 2)|) |(b : ℝ)| := by
  simpa using pell_shifted_intercepts_max (D := 1) (a := -1) (by decide) (by decide) b

-- With D = 3 and a = 2 the vertical intercepts are one unit away from the shift.
example (b : ℤ) :
    2 + Real.sqrt (1 + 3 * (b : ℝ) ^ 2) =
      max (max |2 + Real.sqrt (1 + 3 * (b : ℝ) ^ 2)|
        |2 - Real.sqrt (1 + 3 * (b : ℝ) ^ 2)|) (max |(b : ℝ) + 1| |(b : ℝ) - 1|) := by
  have h := pell_shifted_intercepts_max (D := 3) (a := 2) (by decide) (by decide) b
  norm_num at h
  simpa using h

end MetaMathlibExt.pell_shifted_intercepts_max
