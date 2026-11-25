/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuarticToCubic

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

-- The quartic point (−2, 0) gives a point away from the origin even on this singular cubic.
example : ∃ X Y : ℤ, X ≠ 0 ∧ Y ^ 2 = X ^ 3 + 8 * X ^ 2 := by
  simpa using exists_int_point_elliptic_of_exists_int_point_quartic (-2) 8 0
    (by decide) ⟨-2, 0, by decide⟩

end MathlibExt.NumberTheory.PowerfulNumbersWanted
