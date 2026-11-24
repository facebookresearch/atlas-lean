/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Padics.MultivariableHensel

/-!
# Test of multivariable Hensel lifting

At `(2, 0)` the polynomial `X₀ X₁ + 2³` has residual `2³` and partial derivative `2` in
the second coordinate. This tests lifting with a nonunit derivative.
-/

namespace MetaMathlibExt

open MvPolynomial

example : ∃ x : Fin 2 → ℤ_[2], x 0 * x 1 + 2 ^ 3 = 0 := by
  let f : MvPolynomial (Fin 2) ℤ_[2] := X 0 * X 1 + C (2 ^ 3)
  obtain ⟨x, hx⟩ := exists_mvPolynomial_eval_eq_zero_of_norm_lt_norm_pderiv_sq f ![2, 0] 1 (by
    have htwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
    simp [f, norm_pow, htwo]
    norm_num)
  exact ⟨x, by simpa [f] using hx⟩

end MetaMathlibExt
