/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive.lean`
and
`P2M/Sol/S_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CupPairing.Defs
import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic.LinearCombination

/-!
# The cup pairing is independent of the chosen primitive

For any primitive `h` of `omega φ ψ`, the rational cup pairing equals
`orientedCuspSum Γ h / (2 * mult Γ)`.
-/

open scoped MatrixGroups

namespace ModularCurve
namespace CupPairing
namespace Indep
open ModularCurve.CupPairing ModularCurve

open ModularCurve.PDPairing

private theorem S_sq : ModularGroup.S * ModularGroup.S = (-1 : SL(2, ℤ)) :=
  ModularGroup.S_mul_S_eq

private theorem S_pow_four : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq ModularGroup.S, S_sq, neg_one_sq]

private theorem ST_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = (-1 : SL(2, ℤ)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_S, ModularGroup.coe_T, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.one_fin_two]

private theorem ST_pow_six : (ModularGroup.S * ModularGroup.T) ^ 6 = (1 : SL(2, ℤ)) := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, ST_pow_three, neg_one_sq]

private theorem hom_T_eq_one (f : SL(2, ℤ) →* Multiplicative ℚ) : f ModularGroup.T = 1 := by
  have hS : f ModularGroup.S = 1 := by
    have h : (f ModularGroup.S) ^ 4 = 1 := by rw [← map_pow, S_pow_four, map_one]
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, smul_eq_zero] at h'
    rcases h' with h' | h'
    · norm_num at h'
    · exact toAdd_eq_zero.mp h'
  have hU : f (ModularGroup.S * ModularGroup.T) = 1 := by
    have h : (f (ModularGroup.S * ModularGroup.T)) ^ 6 = 1 := by
      rw [← map_pow, ST_pow_six, map_one]
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, smul_eq_zero] at h'
    rcases h' with h' | h'
    · norm_num at h'
    · exact toAdd_eq_zero.mp h'
  have : ModularGroup.T = ModularGroup.S⁻¹ * (ModularGroup.S * ModularGroup.T) := by
    rw [inv_mul_cancel_left]
  rw [this, map_mul, map_inv, hS, hU, inv_one, one_mul]

variable (Γ : Subgroup SL(2, ℤ))

private theorem sum_apply_orientedCuspGen_eq_zero [Γ.FiniteIndex] (χ : Additive Γ →+ ℚ) :
    ∑ q : OrientedCusp Γ, χ (Additive.ofMul (orientedCuspGen Γ q)) = 0 := by
  have h := (AddMonoidHom.toMultiplicativeRight χ).transfer_eq_prod_quotient_orbitRel_zpowers_quot
    ModularGroup.T
  rw [hom_T_eq_one] at h
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_one, toAdd_prod] at h'
  rw [h']
  rfl

variable {Γ}

private def diffChar (φ ψ : Additive Γ →+ ℚ) (h₀ h : Γ → ℚ) (hh₀ : IsPrimitive φ ψ h₀)
    (hh : IsPrimitive φ ψ h) : Additive Γ →+ ℚ where
  toFun g := h₀ (Additive.toMul g) - h (Additive.toMul g)
  map_zero' := by
    have e₀ := hh₀ 1 1
    have e := hh 1 1
    rw [one_mul, omega_one_left, sub_zero] at e₀ e
    change h₀ 1 - h 1 = 0
    linear_combination -e₀ + e
  map_add' a b := by
    change h₀ (Additive.toMul a * Additive.toMul b) - h (Additive.toMul a * Additive.toMul b) =
      (h₀ (Additive.toMul a) - h (Additive.toMul a)) + (h₀ (Additive.toMul b) - h (Additive.toMul
          b))
    rw [hh₀, hh]
    ring

private theorem diffChar_apply (φ ψ : Additive Γ →+ ℚ) (h₀ h : Γ → ℚ) (hh₀ : IsPrimitive φ ψ h₀)
    (hh : IsPrimitive φ ψ h) (g : Γ) :
    diffChar φ ψ h₀ h hh₀ hh (Additive.ofMul g) = h₀ g - h g := rfl

private theorem orientedCuspSum_eq_of_isPrimitive [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ)
    (h₀ h : Γ → ℚ) (hh₀ : IsPrimitive φ ψ h₀) (hh : IsPrimitive φ ψ h) :
    orientedCuspSum Γ h₀ = orientedCuspSum Γ h := by
  have hsplit : h₀ = h + (fun g => diffChar φ ψ h₀ h hh₀ hh (Additive.ofMul g)) := by
    funext g
    simp only [Pi.add_apply, diffChar_apply]
    ring
  rw [hsplit, orientedCuspSum_add]
  unfold orientedCuspSum
  rw [sum_apply_orientedCuspGen_eq_zero Γ (diffChar φ ψ h₀ h hh₀ hh), add_zero]

private theorem main [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ) (h : Γ → ℚ) (hh : IsPrimitive φ ψ h) :
    pair Γ φ ψ = orientedCuspSum Γ h / (2 * mult Γ) := by
  have hp : ∃ h' : Γ → ℚ, IsPrimitive φ ψ h' := ⟨h, hh⟩
  rw [pair_eq_dif Γ φ ψ hp, orientedCuspSum_eq_of_isPrimitive φ ψ _ h (Classical.choose_spec hp) hh]

end ModularCurve.CupPairing.Indep

/-- For any primitive `h` of `omega φ ψ`, the cup pairing is `orientedCuspSum Γ h / (2 * mult Γ)`:
the value does not depend on the chosen primitive. -/
public theorem ModularCurve.CupPairing.pair_eq_orientedCuspSum_div_of_isPrimitive
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ) (h : Γ → ℚ)
    (hh : ModularCurve.CupPairing.IsPrimitive φ ψ h) :
    ModularCurve.CupPairing.pair Γ φ ψ =
      ModularCurve.PDPairing.orientedCuspSum Γ h / (2 * ModularCurve.CupPairing.mult Γ) :=
  ModularCurve.CupPairing.Indep.main φ ψ h hh
