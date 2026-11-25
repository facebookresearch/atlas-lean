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

end MetaMathlibExt.pell_inverse_closed_form
