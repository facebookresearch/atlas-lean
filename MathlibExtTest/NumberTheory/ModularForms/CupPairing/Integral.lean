/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CupPairing.Integral

@[expose] public section

open scoped MatrixGroups

/-- Source consumer with the original binders. -/
private theorem exactSource (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ IP : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ℤ,
      Function.Bijective IP ∧ Function.Bijective IP.flip ∧
      ∀ x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
        (IP x y : ℚ) = ModularCurve.CupPairing.pair Γ
          ((Int.castAddHom ℚ).comp (x : Additive Γ →+ ℤ))
          ((Int.castAddHom ℚ).comp (y : Additive Γ →+ ℤ)) :=
  ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair Γ

/-- Outside finite index the rational pairing is defined to be `0`, so the finite-index
hypothesis is what makes the comparison meaningful. -/
example (Γ : Subgroup SL(2, ℤ)) (hΓ : ¬ Γ.FiniteIndex) (φ ψ : Additive Γ →+ ℚ) :
    ModularCurve.CupPairing.pair Γ φ ψ = 0 :=
  ModularCurve.CupPairing.pair_eq_zero_of_not_finiteIndex Γ φ ψ hΓ

/-- The level-one instance. -/
example : ∃ IP : ModularCurve.Period.parabolicHoms ℤ (⊤ : Subgroup SL(2, ℤ)) ℤ →ₗ[ℤ]
        ModularCurve.Period.parabolicHoms ℤ (⊤ : Subgroup SL(2, ℤ)) ℤ →ₗ[ℤ] ℤ,
      Function.Bijective IP ∧ Function.Bijective IP.flip ∧
      ∀ x y : ModularCurve.Period.parabolicHoms ℤ (⊤ : Subgroup SL(2, ℤ)) ℤ,
        (IP x y : ℚ) = ModularCurve.CupPairing.pair ⊤
          ((Int.castAddHom ℚ).comp (x : Additive (⊤ : Subgroup SL(2, ℤ)) →+ ℤ))
          ((Int.castAddHom ℚ).comp (y : Additive (⊤ : Subgroup SL(2, ℤ)) →+ ℤ)) :=
  exactSource ⊤
