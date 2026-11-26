/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46

/-! # Tests for `MathlibExt.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46` -/

namespace MathlibExtTest.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46

open MathlibExt.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46Wanted

-- Restricting both transvections to elementary ones gives a negative answer.
example : ¬ doubleCommutatorWithTransvectionsUnipotent :=
  doubleCommutatorWithTransvectionsUnipotent_refuted

/-- The elementary transvection `1 + 2 e₀₁` in `GL₃(ℤ)`, with inverse `1 - 2 e₀₁`. -/
private def t : GL (Fin 3) ℤ :=
  ⟨1 + Matrix.single 0 1 2, 1 - Matrix.single 0 1 2, by decide, by decide⟩

private theorem isElementaryTransvection_t : IsElementaryTransvection t :=
  ⟨0, 1, 2, by decide, by decide, rfl⟩

-- The identity is not an elementary transvection: the coefficient `r` must be nonzero.
example : ¬ IsElementaryTransvection (1 : GL (Fin 3) ℤ) := by
  rintro ⟨i, j, r, hij, hr, h⟩
  have hij' := congrFun (congrFun h i) j
  simp [Matrix.one_apply_ne hij] at hij'
  exact hr hij'.symm

-- Over the zero ring every coefficient vanishes, so there are no elementary transvections; this
-- is why the question assumes `R` nontrivial.
example (τ : GL (Fin 3) PUnit) : ¬ IsElementaryTransvection τ := by
  rintro ⟨i, j, r, -, hr, -⟩
  exact hr (Subsingleton.elim r 0)

-- For `σ = 1` the double commutator `[[1, t], t]` is the identity, which is unipotent: the
-- property in the question holds for some `σ`, so the refutation depends on the choice of `σ`.
example : ∃ τ₁ τ₂ : GL (Fin 3) ℤ, IsElementaryTransvection τ₁ ∧ IsElementaryTransvection τ₂ ∧
    IsNilpotent (((((1 : GL (Fin 3) ℤ) * τ₁ * 1⁻¹ * τ₁⁻¹) * τ₂ *
      ((1 : GL (Fin 3) ℤ) * τ₁ * 1⁻¹ * τ₁⁻¹)⁻¹ * τ₂⁻¹ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) -
        1) :=
  ⟨t, t, isElementaryTransvection_t, isElementaryTransvection_t, by simp⟩

end MathlibExtTest.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46
