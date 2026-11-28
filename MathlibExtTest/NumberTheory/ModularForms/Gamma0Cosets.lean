/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.Gamma0Cosets

/-!
# Tests for `MathlibExt.NumberTheory.ModularForms.Gamma0Cosets`
-/

set_option autoImplicit false

@[expose] public section

open Matrix MatrixGroups CongruenceSubgroup

#check @WLight.gamma0RightCosetsEquiv
#check @WLight.gamma0RightCosetsEquiv_mk_eq_iff
#check @WLight.exists_mul_eq_gamma0RightCosetsEquiv
#check @WLight.index_gamma0_eq_card_modularPolynomialReps
#check @WLight.card_modularPolynomialReps

/-- The trivial coset `Γ₀(5)` corresponds to `!![5, 0; 0, 1] ∈ C_5`. -/
example : WLight.gamma0RightCosetsEquiv 5 (Quotient.mk _ 1) =
    ⟨!![5, 0; 0, 1], by
      rw [WLight.mem_modularPolynomialReps]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      decide⟩ := by
  rw [WLight.gamma0RightCosetsEquiv_mk_eq_iff]
  exact ⟨1, by simp⟩

/-- `#C_6 = ψ(6) = 12`, via multiplicativity of `ψ`. -/
example : (WLight.modularPolynomialReps 6).card = 12 := by
  rw [WLight.card_modularPolynomialReps, show (6 : ℕ) = 2 * 3 by norm_num,
    ArithmeticFunction.isMultiplicative_dedekindPsi.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.dedekindPsi_prime Nat.prime_two,
    ArithmeticFunction.dedekindPsi_prime Nat.prime_three]
  norm_num

/-- `[SL₂(ℤ) : Γ₀(p)] = p + 1` for a prime `p`, from `#C_p = p + 1`. -/
example {p : ℕ} (hp : p.Prime) : (Gamma0 p).index = p + 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [WLight.index_gamma0_eq_card_modularPolynomialReps, WLight.card_modularPolynomialReps_prime hp]
