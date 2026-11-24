/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellShiftedQuadrants

namespace MetaMathlibExt.pell_shifted_real_solutions_eventually_in_quadrants

private def fundamental : Pell.Solution₁ 3 := .mk 2 1 (by decide)

private theorem isFundamental : Pell.IsFundamental fundamental :=
  ⟨by decide, by decide, fun {_} hx => hx⟩

-- With shifts (-4, 3), the fourth branch starts outside its eventual quadrant.
-- On a common tail the two lower branches have opposite horizontal signs.
example :
    ¬ (0 ≤ pellU 3 2 1 0 - 4 ∧ -pellV 3 2 1 0 + 3 ≤ 0) ∧
    ∀ᶠ x : ℝ in Filter.atTop,
      (-pellU 3 2 1 x - 4 ≤ 0 ∧ -pellV 3 2 1 x + 3 ≤ 0) ∧
      (0 ≤ pellU 3 2 1 x - 4 ∧ -pellV 3 2 1 x + 3 ≤ 0) := by
  constructor
  · norm_num [pellU_zero, pellV_zero]
  · filter_upwards [pell_shifted_real_solutions_eventually_in_quadrants isFundamental (-4) 3]
      with x hx
    simpa [fundamental, sub_eq_add_neg] using hx.2.2

end MetaMathlibExt.pell_shifted_real_solutions_eventually_in_quadrants
