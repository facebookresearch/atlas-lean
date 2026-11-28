/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JFunctionQExpansion

open UpperHalfPlane

#check @WLight.jFunction_qExpansion_int

/-- The first coefficient after the constant term is `196884`, and the expansion holds at
`τ = i`. -/
example : ∃ c : ℕ → ℤ, c 0 = 196884 ∧
    WLight.jFunction UpperHalfPlane.I = (Function.Periodic.qParam 1 UpperHalfPlane.I)⁻¹ + 744 +
      ∑' n : ℕ, (c n : ℂ) * Function.Periodic.qParam 1 UpperHalfPlane.I ^ (n + 1) := by
  obtain ⟨c, hc, h⟩ := WLight.jFunction_qExpansion_int
  exact ⟨c, hc, (h UpperHalfPlane.I).2⟩
