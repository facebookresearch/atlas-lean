/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomialReps

/-!
# Tests for `MathlibExt.NumberTheory.ModularForms.ModularPolynomialReps`
-/

set_option autoImplicit false

@[expose] public section

open Matrix MatrixGroups

#check @WLight.modularPolynomialReps
#check @WLight.mem_modularPolynomialReps
#check @WLight.exists_eq_mul_of_det
#check @WLight.modularPolynomialReps_eq_of_mul_eq
#check @WLight.modularPolynomialReps_exists_equiv_mul_eq
#check @WLight.modularPolynomialReps_prime
#check @WLight.card_modularPolynomialReps_prime

/-- `C_2` has `3` elements. -/
example : (WLight.modularPolynomialReps 2).card = 3 :=
  WLight.card_modularPolynomialReps_prime Nat.prime_two

/-- `C_7` has `8` elements. -/
example : (WLight.modularPolynomialReps 7).card = 8 :=
  WLight.card_modularPolynomialReps_prime (by decide)

/-- For `N = 4`, `!![2, 1; 0, 2]` is primitive and lies in `C_4`. -/
example : !![(2 : ℤ), 1; 0, 2] ∈ WLight.modularPolynomialReps 4 := by
  rw [WLight.mem_modularPolynomialReps]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  decide

/-- For `N = 4`, `!![2, 0; 0, 2]` is not primitive and is not in `C_4`. -/
example : !![(2 : ℤ), 0; 0, 2] ∉ WLight.modularPolynomialReps 4 := by
  rw [WLight.mem_modularPolynomialReps]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  decide

/-- For every `γ ∈ SL₂(ℤ)`, right multiplication by `γ` permutes the orbits of `C_5`. -/
example (γ : SL(2, ℤ)) :
    ∃ σ : WLight.modularPolynomialReps 5 ≃ WLight.modularPolynomialReps 5,
      ∃ δ : WLight.modularPolynomialReps 5 → SL(2, ℤ), ∀ M : WLight.modularPolynomialReps 5,
        (M : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
          (δ M : Matrix (Fin 2) (Fin 2) ℤ) * (σ M : Matrix (Fin 2) (Fin 2) ℤ) :=
  WLight.modularPolynomialReps_exists_equiv_mul_eq 5 γ
