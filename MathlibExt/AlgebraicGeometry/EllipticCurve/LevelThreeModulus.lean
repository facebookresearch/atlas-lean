/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_LevelThreeModulus.lean`
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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public section

/-!
# Level-three modulus and the Deuring form
-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

def deuringCurve (α β : R) : WeierstrassCurve R := ⟨α, 0, β, 0, 0⟩

section deuringCurve

variable (α β : R)

@[simp] theorem deuringCurve_a₁ : (deuringCurve α β).a₁ = α := rfl
@[simp] theorem deuringCurve_a₂ : (deuringCurve α β).a₂ = 0 := rfl
@[simp] theorem deuringCurve_a₃ : (deuringCurve α β).a₃ = β := rfl
@[simp] theorem deuringCurve_a₄ : (deuringCurve α β).a₄ = 0 := rfl
@[simp] theorem deuringCurve_a₆ : (deuringCurve α β).a₆ = 0 := rfl

theorem deuringCurve_b₂ : (deuringCurve α β).b₂ = α ^ 2 := by
  simp [deuringCurve, WeierstrassCurve.b₂]

theorem deuringCurve_b₄ : (deuringCurve α β).b₄ = α * β := by
  simp [deuringCurve, WeierstrassCurve.b₄]

theorem deuringCurve_b₆ : (deuringCurve α β).b₆ = β ^ 2 := by
  simp [deuringCurve, WeierstrassCurve.b₆]

theorem deuringCurve_b₈ : (deuringCurve α β).b₈ = 0 := by
  simp [deuringCurve, WeierstrassCurve.b₈]

theorem deuringCurve_c₄ : (deuringCurve α β).c₄ = α * (α ^ 3 - 24 * β) := by
  simp only [WeierstrassCurve.c₄, deuringCurve_b₂, deuringCurve_b₄]; ring

theorem deuringCurve_Δ : (deuringCurve α β).Δ = β ^ 3 * (α ^ 3 - 27 * β) := by
  simp only [WeierstrassCurve.Δ, deuringCurve_b₂, deuringCurve_b₄, deuringCurve_b₆, deuringCurve_b₈]
  ring

theorem deuringCurve_map {S : Type*} [CommRing S] (f : R →+* S) :
    (deuringCurve α β).map f = deuringCurve (f α) (f β) := by
  simp [deuringCurve, WeierstrassCurve.map]

theorem deuringCurve_Δ_of_levelThree_rel {τ ν : R} (h : 3 * ν + τ ^ 2 + 3 * τ + 3 = 0) :
    (deuringCurve τ ν).Δ = ν ^ 3 * (τ + 3) ^ 3 := by
  rw [deuringCurve_Δ]
  have : τ ^ 3 - 27 * ν = (τ + 3) ^ 3 := by linear_combination (-9 : R) * h
  rw [this]

end deuringCurve

variable (W : WeierstrassCurve R)

def deuringA₃ (x y : R) : R := 2 * y + W.a₁ * x + W.a₃

def tangentSlopeNum (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

noncomputable def tangentSlope (x y : R) : R := W.tangentSlopeNum x y * Ring.inverse (W.deuringA₃ x
  y)

noncomputable def deuringA₁ (x y : R) : R := W.a₁ + 2 * W.tangentSlope x y

def flexForm (x y : R) : R :=
  W.tangentSlopeNum x y ^ 2 + W.a₁ * W.tangentSlopeNum x y * W.deuringA₃ x y
    - (W.a₂ + 3 * x) * W.deuringA₃ x y ^ 2

noncomputable def deuringVariableChange (x₁ y₁ : R) (u : Rˣ) : VariableChange R :=
  ⟨u, x₁, W.tangentSlope x₁ y₁, y₁⟩

noncomputable def levelThreeModulus (x₁ y₁ x₂ : R) : R :=
  W.deuringA₁ x₁ y₁ * (x₂ - x₁) * Ring.inverse (W.deuringA₃ x₁ y₁)

noncomputable def levelThreeAbscissa (x₁ y₁ x₂ : R) : R :=
  (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 2

noncomputable def levelThreeOrdinate (x₁ y₁ x₂ y₂ : R) : R :=
  (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^
    3

section ring

variable {W}

theorem deuringA₃_def (x y : R) : W.deuringA₃ x y = 2 * y + W.a₁ * x + W.a₃ := rfl

theorem tangentSlopeNum_def (x y : R) :
    W.tangentSlopeNum x y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := rfl

theorem tangentSlope_def (x y : R) :
    W.tangentSlope x y = W.tangentSlopeNum x y * Ring.inverse (W.deuringA₃ x y) := rfl

theorem deuringA₁_def (x y : R) : W.deuringA₁ x y = W.a₁ + 2 * W.tangentSlope x y := rfl

theorem flexForm_def (x y : R) : W.flexForm x y =
    W.tangentSlopeNum x y ^ 2 + W.a₁ * W.tangentSlopeNum x y * W.deuringA₃ x y
      - (W.a₂ + 3 * x) * W.deuringA₃ x y ^ 2 := rfl

theorem levelThreeModulus_def (x₁ y₁ x₂ : R) : W.levelThreeModulus x₁ y₁ x₂ =
    W.deuringA₁ x₁ y₁ * (x₂ - x₁) * Ring.inverse (W.deuringA₃ x₁ y₁) := rfl

theorem levelThreeAbscissa_def (x₁ y₁ x₂ : R) : W.levelThreeAbscissa x₁ y₁ x₂ =
    (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 2 := rfl

theorem levelThreeOrdinate_def (x₁ y₁ x₂ y₂ : R) : W.levelThreeOrdinate x₁ y₁ x₂ y₂ =
    (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3
      * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 3 := rfl

@[simp] theorem deuringVariableChange_u (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).u = u := rfl
@[simp] theorem deuringVariableChange_r (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).r = x₁ := rfl
@[simp] theorem deuringVariableChange_s (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).s = W.tangentSlope x₁ y₁ := rfl
@[simp] theorem deuringVariableChange_t (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).t = y₁ := rfl

theorem deuringA₃_eq_evalEval_polynomialY (x y : R) :
    W.deuringA₃ x y = W.toAffine.polynomialY.evalEval x y := by
  rw [Affine.evalEval_polynomialY]; rfl

theorem deuringA₃_eq_sub_negY (x y : R) : W.deuringA₃ x y = y - W.toAffine.negY x y := by
  rw [deuringA₃_def, Affine.negY]; change 2 * y + W.a₁ * x + W.a₃ = y - (-y - W.a₁ * x - W.a₃); ring

theorem tangentSlopeNum_eq_neg_evalEval_polynomialX (x y : R) :
    W.tangentSlopeNum x y = -W.toAffine.polynomialX.evalEval x y := by
  rw [Affine.evalEval_polynomialX, tangentSlopeNum_def]; change _ = -(W.a₁ * y - _); ring

theorem eval_Ψ₃ (x : R) :
    W.Ψ₃.eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  simp only [Ψ₃, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat]

theorem flexForm_add_eval_Ψ₃ (x y : R) :
    W.flexForm x y + W.Ψ₃.eval x = -(W.b₂ + 12 * x) * W.toAffine.polynomial.evalEval x y := by
  rw [eval_Ψ₃, Affine.evalEval_polynomial, flexForm_def, tangentSlopeNum_def, deuringA₃_def]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  change _ = -(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) *
    (y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  ring

theorem flexForm_eq_neg_eval_Ψ₃ {x y : R} (h : W.toAffine.Equation x y) :
    W.flexForm x y = -W.Ψ₃.eval x := by
  have := flexForm_add_eval_Ψ₃ (W := W) x y
  rw [show W.toAffine.polynomial.evalEval x y = 0 from h, mul_zero] at this
  linear_combination this

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem map_ringInverse_of_isUnit {a : R} (h : IsUnit a) : f (Ring.inverse a) = Ring.inverse (f a)
  := by
  obtain ⟨u, rfl⟩ := h
  rw [Ring.inverse_unit, show f (u : R) = ((Units.map (f : R →* S) u : Sˣ) : S) from rfl,
    Ring.inverse_unit]
  rfl

theorem deuringA₃_map (x y : R) : (W.map f).deuringA₃ (f x) (f y) = f (W.deuringA₃ x y) := by
  simp [deuringA₃_def, map_ofNat]

theorem tangentSlopeNum_map (x y : R) :
    (W.map f).tangentSlopeNum (f x) (f y) = f (W.tangentSlopeNum x y) := by
  simp [tangentSlopeNum_def, map_ofNat]

theorem flexForm_map (x y : R) : (W.map f).flexForm (f x) (f y) = f (W.flexForm x y) := by
  simp [flexForm_def, tangentSlopeNum_map, deuringA₃_map, map_ofNat]

theorem tangentSlope_map_of_isUnit {x y : R} (h : IsUnit (W.deuringA₃ x y)) :
    (W.map f).tangentSlope (f x) (f y) = f (W.tangentSlope x y) := by
  rw [tangentSlope_def, tangentSlope_def, tangentSlopeNum_map, deuringA₃_map, map_mul,
    map_ringInverse_of_isUnit f h]

theorem deuringA₁_map_of_isUnit {x y : R} (h : IsUnit (W.deuringA₃ x y)) :
    (W.map f).deuringA₁ (f x) (f y) = f (W.deuringA₁ x y) := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_map_of_isUnit f h]; simp [map_ofNat]

theorem levelThreeModulus_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ : R) :
    (W.map f).levelThreeModulus (f x₁) (f y₁) (f x₂) = f (W.levelThreeModulus x₁ y₁ x₂) := by
  rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₁_map_of_isUnit f h, deuringA₃_map,
    ← map_ringInverse_of_isUnit f h]
  simp

theorem levelThreeAbscissa_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ : R) :
    (W.map f).levelThreeAbscissa (f x₁) (f y₁) (f x₂) = f (W.levelThreeAbscissa x₁ y₁ x₂) := by
  rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_map, ← map_ringInverse_of_isUnit f
    h]
  simp

theorem levelThreeOrdinate_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ y₂ : R) :
    (W.map f).levelThreeOrdinate (f x₁) (f y₁) (f x₂) (f y₂) = f (W.levelThreeOrdinate x₁ y₁ x₂ y₂)
      := by
  rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_map, tangentSlope_map_of_isUnit f h,
    ← map_ringInverse_of_isUnit f h]
  simp

end map

theorem deuringA₃_variableChange (C : VariableChange R) (x y : R) :
    W.deuringA₃ ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).deuringA₃ x y := by
  simp only [deuringA₃_def, variableChange_a₁, variableChange_a₃]
  linear_combination -((W.a₁ + 2 * C.s) * x * (C.u : R) ^ 2) * C.u.inv_mul
    - (W.a₃ + C.r * W.a₁ + 2 * C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul

theorem tangentSlopeNum_variableChange (C : VariableChange R) (x y : R) :
    W.tangentSlopeNum ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 4 * (C • W).tangentSlopeNum x y + C.s * (C.u : R) ^ 3 * (C • W).deuringA₃ x y
        := by
  simp only [tangentSlopeNum_def, deuringA₃_def, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄]
  linear_combination -(2 * (C.u : R) ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * x)
      * pow_mul_pow_eq_one 2 C.u.inv_mul
    - (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t)
      * pow_mul_pow_eq_one 4 C.u.inv_mul
    + ((C.u : R) ^ 3 * (W.a₁ + 2 * C.s) * y - C.s * (C.u : R) ^ 2 * (W.a₁ + 2 * C.s) * x)
      * C.u.inv_mul
    - C.s * (W.a₃ + C.r * W.a₁ + 2 * C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul

theorem flexForm_variableChange (C : VariableChange R) (x y : R) :
    W.flexForm ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 8 * (C • W).flexForm x y := by
  rw [flexForm_def, flexForm_def, tangentSlopeNum_variableChange, deuringA₃_variableChange]
  have ha₁ : W.a₁ = (C.u : R) * (C • W).a₁ - 2 * C.s := by
    rw [variableChange_a₁]; linear_combination -(W.a₁ + 2 * C.s) * C.u.inv_mul
  have ha₂ : W.a₂ + 3 * ((C.u : R) ^ 2 * x + C.r)
      = (C.u : R) ^ 2 * ((C • W).a₂ + 3 * x) + C.s * W.a₁ + C.s ^ 2 := by
    rw [variableChange_a₂]
    linear_combination -(W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * pow_mul_pow_eq_one 2 C.u.inv_mul
  rw [ha₂, ha₁]
  ring

end ring

section field

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

theorem tangentSlope_eq_div (x y : F) :
    W.tangentSlope x y = W.tangentSlopeNum x y / W.deuringA₃ x y := by
  rw [tangentSlope_def, Ring.inverse_eq_inv, div_eq_mul_inv]

theorem tangentSlope_eq_slope [DecidableEq F] {x y : F} (h : W.deuringA₃ x y ≠ 0) :
    W.tangentSlope x y = W.toAffine.slope x x y y := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy; apply h; rw [deuringA₃_eq_sub_negY, ← hy, sub_self]
  rw [Affine.slope_of_Y_ne rfl hy, ← deuringA₃_eq_sub_negY, tangentSlope_eq_div]; rfl

theorem deuringA₁_eq_div (x y : F) :
    W.deuringA₁ x y = (W.a₁ * W.deuringA₃ x y + 2 * W.tangentSlopeNum x y) / W.deuringA₃ x y ∨
      W.deuringA₃ x y = 0 := by
  by_cases h : W.deuringA₃ x y = 0
  · exact Or.inr h
  · left; rw [deuringA₁_def, tangentSlope_eq_div]; field_simp

theorem levelThreeModulus_eq_div (x₁ y₁ x₂ : F) : W.levelThreeModulus x₁ y₁ x₂ =
    (W.a₁ * W.deuringA₃ x₁ y₁ + 2 * W.tangentSlopeNum x₁ y₁) * (x₂ - x₁) / W.deuringA₃ x₁ y₁ ^ 2 :=
      by
  rw [levelThreeModulus_def, deuringA₁_def, tangentSlope_eq_div, Ring.inverse_eq_inv]
  by_cases h : W.deuringA₃ x₁ y₁ = 0
  · rw [h]; simp
  · field_simp

theorem levelThreeAbscissa_eq_div (x₁ y₁ x₂ : F) :
    W.levelThreeAbscissa x₁ y₁ x₂ = (x₂ - x₁) ^ 3 / W.deuringA₃ x₁ y₁ ^ 2 := by
  rw [levelThreeAbscissa_def, Ring.inverse_eq_inv, div_eq_mul_inv, inv_pow]

theorem levelThreeOrdinate_eq_div (x₁ y₁ x₂ y₂ : F) : W.levelThreeOrdinate x₁ y₁ x₂ y₂ =
    (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3 / W.deuringA₃ x₁ y₁ ^ 3 := by
  rw [levelThreeOrdinate_def, Ring.inverse_eq_inv, div_eq_mul_inv, inv_pow]

section map

variable {K : Type*} [Field K] (φ : F →+* K)

theorem tangentSlope_map (x y : F) : (W.map φ).tangentSlope (φ x) (φ y) = φ (W.tangentSlope x y) :=
  by
  rw [tangentSlope_eq_div, tangentSlope_eq_div, tangentSlopeNum_map, deuringA₃_map, map_div₀]

theorem deuringA₁_map (x y : F) : (W.map φ).deuringA₁ (φ x) (φ y) = φ (W.deuringA₁ x y) := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_map]; simp [map_ofNat]

theorem levelThreeModulus_map (x₁ y₁ x₂ : F) :
    (W.map φ).levelThreeModulus (φ x₁) (φ y₁) (φ x₂) = φ (W.levelThreeModulus x₁ y₁ x₂) := by
  rw [levelThreeModulus_eq_div, levelThreeModulus_eq_div, tangentSlopeNum_map, deuringA₃_map]
  simp [map_ofNat, map_div₀]

theorem levelThreeAbscissa_map (x₁ y₁ x₂ : F) :
    (W.map φ).levelThreeAbscissa (φ x₁) (φ y₁) (φ x₂) = φ (W.levelThreeAbscissa x₁ y₁ x₂) := by
  rw [levelThreeAbscissa_eq_div, levelThreeAbscissa_eq_div, deuringA₃_map]
  simp [map_div₀]

theorem levelThreeOrdinate_map (x₁ y₁ x₂ y₂ : F) :
    (W.map φ).levelThreeOrdinate (φ x₁) (φ y₁) (φ x₂) (φ y₂) = φ (W.levelThreeOrdinate x₁ y₁ x₂ y₂)
      := by
  rw [levelThreeOrdinate_eq_div, levelThreeOrdinate_eq_div, deuringA₃_map, tangentSlope_map]
  simp [map_div₀]

end map

theorem deuringVariableChange_smul {x₁ y₁ : F} (heq : W.toAffine.Equation x₁ y₁)
    (hΨ : W.deuringA₃ x₁ y₁ ≠ 0) (hflex : W.flexForm x₁ y₁ = 0) (u : Fˣ) :
    W.deuringVariableChange x₁ y₁ u • W =
      deuringCurve (W.deuringA₁ x₁ y₁ / u) (W.deuringA₃ x₁ y₁ / (u : F) ^ 3) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  rw [Affine.equation_iff] at heq
  set m := W.tangentSlope x₁ y₁ with hm
  have hmd : m * W.deuringA₃ x₁ y₁ = W.tangentSlopeNum x₁ y₁ := by
    rw [hm, tangentSlope_eq_div, div_mul_cancel₀ _ hΨ]
  have hfl : m ^ 2 + W.a₁ * m - W.a₂ - 3 * x₁ = 0 := by
    have h : (m ^ 2 + W.a₁ * m - W.a₂ - 3 * x₁) * W.deuringA₃ x₁ y₁ ^ 2 = W.flexForm x₁ y₁ := by
      rw [flexForm_def, ← hmd]; ring
    rw [hflex] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hΨ)
  rw [deuringA₃_def] at hmd hΨ
  rw [tangentSlopeNum_def] at hmd
  ext
  · simp only [variableChange_a₁, deuringVariableChange, deuringCurve_a₁, deuringA₁_def,
      Units.val_inv_eq_inv_val, ← hm]
    field_simp
  · simp only [variableChange_a₂, deuringVariableChange, deuringCurve_a₂, Units.val_inv_eq_inv_val,
      ← hm]
    rw [show W.a₂ - m * W.a₁ + 3 * x₁ - m ^ 2 = 0 by linear_combination -hfl, mul_zero]
  · simp only [variableChange_a₃, deuringVariableChange, deuringCurve_a₃, deuringA₃_def,
      Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [variableChange_a₄, deuringVariableChange, deuringCurve_a₄, Units.val_inv_eq_inv_val,
      ← hm]
    rw [show W.a₄ - m * W.a₃ + 2 * x₁ * W.a₂ - (y₁ + x₁ * m) * W.a₁ + 3 * x₁ ^ 2 - 2 * m * y₁ = 0 by
      linear_combination -hmd, mul_zero]
  · simp only [variableChange_a₆, deuringVariableChange, deuringCurve_a₆, Units.val_inv_eq_inv_val]
    rw [show W.a₆ + x₁ * W.a₄ + x₁ ^ 2 * W.a₂ + x₁ ^ 3 - y₁ * W.a₃ - y₁ ^ 2 - x₁ * y₁ * W.a₁ = 0 by
      linear_combination -heq, mul_zero]

theorem deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus {x₁ y₁ x₂ : F}
    (heq : W.toAffine.Equation x₁ y₁) (hΨ : W.deuringA₃ x₁ y₁ ≠ 0) (hflex : W.flexForm x₁ y₁ = 0)
    (hx : x₁ ≠ x₂) (u : Fˣ) (hu : (u : F) = W.deuringA₃ x₁ y₁ / (x₂ - x₁)) :
    W.deuringVariableChange x₁ y₁ u • W =
      deuringCurve (W.levelThreeModulus x₁ y₁ x₂) (W.levelThreeAbscissa x₁ y₁ x₂) := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [deuringVariableChange_smul heq hΨ hflex u, hu, levelThreeModulus_def, levelThreeAbscissa_def,
    Ring.inverse_eq_inv]
  congr 1
  · field_simp
  · field_simp

theorem tangentSlope_variableChange (C : VariableChange F) {x y : F} (h : (C • W).deuringA₃ x y ≠
  0) :
    W.tangentSlope ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) * (C • W).tangentSlope x y + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [tangentSlope_eq_div, tangentSlope_eq_div, tangentSlopeNum_variableChange,
    deuringA₃_variableChange]
  field_simp

theorem deuringA₁_variableChange (C : VariableChange F) {x y : F} (h : (C • W).deuringA₃ x y ≠ 0) :
    W.deuringA₁ ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) * (C • W).deuringA₁ x y := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_variableChange C h, variableChange_a₁,
    Units.val_inv_eq_inv_val]
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  field_simp
  ring

theorem levelThreeModulus_variableChange (C : VariableChange F) (x₁ y₁ x₂ : F) :
    W.levelThreeModulus ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ +
      C.t)
        ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).levelThreeModulus x₁ y₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₃_variableChange,
      deuringA₁_variableChange C h, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    field_simp
    ring

theorem levelThreeAbscissa_variableChange (C : VariableChange F) (x₁ y₁ x₂ : F) :
    W.levelThreeAbscissa ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁
      + C.t)
        ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).levelThreeAbscissa x₁ y₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_variableChange,
    Ring.inverse_eq_inv,
      Ring.inverse_eq_inv]
    field_simp
    ring

theorem levelThreeOrdinate_variableChange (C : VariableChange F) (x₁ y₁ x₂ y₂ : F) :
    W.levelThreeOrdinate ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁
      + C.t)
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C • W).levelThreeOrdinate x₁ y₁ x₂ y₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_variableChange,
      tangentSlope_variableChange C h, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    field_simp
    ring

theorem deuringA₃_deuringCurve_zero (τ ν : F) : (deuringCurve τ ν).deuringA₃ 0 0 = ν := by
  simp [deuringA₃_def]

theorem tangentSlope_deuringCurve_zero (τ ν : F) : (deuringCurve τ ν).tangentSlope 0 0 = 0 := by
  simp [tangentSlope_eq_div, tangentSlopeNum_def]

theorem levelThreeModulus_deuringCurve {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeModulus 0 0 ν = τ := by
  rw [levelThreeModulus_def, deuringA₁_def, tangentSlope_deuringCurve_zero,
    deuringA₃_deuringCurve_zero,
    Ring.inverse_eq_inv]
  simp only [deuringCurve_a₁, mul_zero, add_zero, sub_zero]
  field_simp

theorem levelThreeAbscissa_deuringCurve {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeAbscissa 0 0 ν = ν := by
  rw [levelThreeAbscissa_eq_div, deuringA₃_deuringCurve_zero, sub_zero]
  field_simp

theorem levelThreeOrdinate_deuringCurve {τ ν : F} (hν : ν ≠ 0) (η : F) :
    (deuringCurve τ ν).levelThreeOrdinate 0 0 ν η = η := by
  rw [levelThreeOrdinate_eq_div, deuringA₃_deuringCurve_zero, tangentSlope_deuringCurve_zero]
  field_simp
  ring

theorem flexForm_deuringCurve (τ ν η : F) :
    (deuringCurve τ ν).flexForm ν η =
      -(τ ^ 2 + 12 * ν) * (deuringCurve τ ν).toAffine.polynomial.evalEval ν η
        - ν ^ 3 * (3 * ν + τ ^ 2 + 3 * τ + 3) := by
  rw [Affine.evalEval_polynomial, flexForm_def, tangentSlopeNum_def, deuringA₃_def]
  simp only [deuringCurve_a₁, deuringCurve_a₂, deuringCurve_a₃, deuringCurve_a₄, deuringCurve_a₆]
  change _ = -(τ ^ 2 + 12 * ν) * (η ^ 2 + τ * ν * η + ν * η - (ν ^ 3 + 0 * ν ^ 2 + 0 * ν + 0)) - _
  ring

end field

end WeierstrassCurve
