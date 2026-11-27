/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.DirichletRealPower

namespace MetaMathlibExt

-- The zeroth power is the convolution unit and the negative first power gives an inverse.
example : ∃ pow : ℝ → ArithmeticFunction ℝ → ArithmeticFunction ℝ,
    ∀ f : ArithmeticFunction ℝ, f 1 = 1 → pow 0 f = 1 ∧ pow (-1) f * f = 1 := by
  obtain ⟨pow, _, laws⟩ := dirichletRealPower_vectorSpace
  refine ⟨pow, fun f hf => ?_⟩
  have add (α β : ℝ) := (laws f f hf hf α β).2.1
  have one := (laws f f hf hf 0 1).2.2.2
  have unit : IsUnit f := ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 (by simp [hf])
  have zero : pow 0 f = 1 := unit.mul_right_cancel (by simpa [one] using (add 0 1).symm)
  exact ⟨zero, by simpa [one, zero] using (add (-1) 1).symm⟩

end MetaMathlibExt
