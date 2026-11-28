/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellRotatedSquare
import Mathlib.Tactic.NormNum.RealSqrt

namespace MetaMathlibExt.pell_solutions_eq_signed_powers

-- For D = 3, (2, 1) is fundamental and (-7, 4) has opposite coordinate signs.
example :
    let a : Pell.Solution₁ 3 := .mk 2 1 (by decide)
    ∃ n : ℕ, ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
      -7 = i * (a ^ n).x ∧ 4 = j * (a ^ n).y := by
  intro a
  have ha : Pell.IsFundamental a := ⟨by decide, by decide, fun {_} hb => hb⟩
  exact (pell_solutions_eq_signed_powers ha (-7) 4).mp (by decide)

-- At exponent zero the negative x sign gives (-1, 0).
example {D : ℤ} {a : Pell.Solution₁ D} (ha : Pell.IsFundamental a) :
    (-1 : ℤ) ^ 2 - D * 0 ^ 2 = 1 := by
  apply (pell_solutions_eq_signed_powers ha (-1) 0).mpr
  exact ⟨0, -1, 1, Or.inr rfl, Or.inl rfl, by simp, by simp⟩

-- The interpolation is defined at D = 0, where its second coordinate vanishes.
example : pellShiftedNorm 0 3 2 (-4) 5 1 (-1) 1 = 6 := by
  norm_num [pellShiftedNorm, pellU, pellV]

-- The square-root term can dominate the other term in the shifted bound.
example : pellShiftBound 3 (-2) 4 = 9 := by
  norm_num [pellShiftBound]

end MetaMathlibExt.pell_solutions_eq_signed_powers
