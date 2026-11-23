/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HataEulerMascheroniFarey
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- Splitting [1/2, 1] at 2/3 leaves a remainder of 1/12.
example : (3 : ℝ) / 2 - 7 / 12 - 5 / 6 = 1 / 12 := by
  obtain ⟨hsplit, hdet⟩ := farey_interval_mediant_telescoping
    (a := 1) (b := 2) (c := 1) (d := 1) (by decide) (by decide) (by decide)
  convert hsplit.trans hdet using 2 <;> norm_num

end MetaMathlibExt
