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
#check @ModularCurve.coeff_jq_zero
#check @ModularCurve.coeff_jq_one

/-- The first coefficient after the constant term is `196884`, and the expansion holds at
`τ = i`. -/
example : ∃ c : ℕ → ℤ, c 0 = 196884 ∧
    WLight.jFunction UpperHalfPlane.I = (Function.Periodic.qParam 1 UpperHalfPlane.I)⁻¹ + 744 +
      ∑' n : ℕ, (c n : ℂ) * Function.Periodic.qParam 1 UpperHalfPlane.I ^ (n + 1) := by
  obtain ⟨c, hc, h⟩ := WLight.jFunction_qExpansion_int
  exact ⟨c, hc, (h UpperHalfPlane.I).2⟩

/-- The coefficients of `q⁻¹`, `q⁰` and `q¹` in the `j` Laurent series are `1`, `744`
and `196884`. -/
example : ModularCurve.jq.coeff (-1) = 1 ∧ ModularCurve.jq.coeff 0 = 744 ∧
    ModularCurve.jq.coeff 1 = 196884 :=
  ⟨ModularCurve.coeff_jq_neg_one, ModularCurve.coeff_jq_zero, ModularCurve.coeff_jq_one⟩
