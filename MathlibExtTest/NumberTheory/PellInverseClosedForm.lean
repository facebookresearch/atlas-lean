/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellInverseClosedForm
import Mathlib.Tactic.NormNum.RealSqrt

namespace MetaMathlibExt.pell_inverse_closed_form

private def fundamental : Pell.Solution₁ 3 := .mk 2 1 (by decide)

private theorem isFundamental : Pell.IsFundamental fundamental :=
  ⟨by decide, by decide, fun {_} hb => hb⟩

-- At x = 1 the inner coordinate is 1 and the logarithm gives exponent zero.
example : pellU 3 2 1 0 + pellV 3 2 1 0 = 1 := by
  have h := (pell_inverse_closed_form isFundamental (x := 1) le_rfl).2
  norm_num [fundamental] at h
  exact h

-- At x = 3 the formula recovers the exponent of the fundamental solution (2, 1).
example : pellU 3 2 1 1 + pellV 3 2 1 1 = 3 := by
  have h := (pell_inverse_closed_form isFundamental (x := 3) (by norm_num)).2
  have hlog : 0 < Real.log (2 + Real.sqrt 3) := Real.log_pos (by linarith [Real.sqrt_nonneg 3])
  norm_num [fundamental, hlog.ne'] at h
  exact h

-- At t = 0, the floor formula gives zero at the lower endpoint x = 1.
example :
    ⌊(Real.log (⌊(1 : ℝ)⌋ : ℝ) + Real.log (2 * Real.sqrt 3 / (1 + Real.sqrt 3))) /
      Real.log (2 + Real.sqrt 3)⌋ = 0 := by
  have h := pell_inverse_floor isFundamental (x := 1) (t := 0) le_rfl le_rfl (by
    rw [pellU_zero, pellV_zero, add_zero])
  simpa [fundamental] using h.symm

-- The first positive Pell threshold x = 3 must be included in the next floor interval.
example :
    ⌊(Real.log (⌊(3 : ℝ)⌋ : ℝ) + Real.log (2 * Real.sqrt 3 / (1 + Real.sqrt 3))) /
      Real.log (2 + Real.sqrt 3)⌋ = 1 := by
  have h := pell_inverse_floor isFundamental (x := 3) (t := 1) (by norm_num) zero_le_one (by
    have hs : (Real.sqrt 3) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    simp only [fundamental, Pell.Solution₁.x_mk, Pell.Solution₁.y_mk, pellU, pellV, Real.rpow_one]
    push_cast
    field_simp [hs]
    ring)
  simpa [fundamental] using h.symm

end MetaMathlibExt.pell_inverse_closed_form
