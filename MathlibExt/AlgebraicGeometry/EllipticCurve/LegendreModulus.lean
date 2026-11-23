/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_LegendreModulus.lean`
`Definitions/Def_WeierstrassCurve_HasseInvariant.lean`
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

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import MathlibExt.AlgebraicGeometry.EllipticCurve.HasseInvariant

@[expose] public section

/-!
# Legendre modulus of a Weierstrass curve
-/

namespace WeierstrassCurve

variable {F : Type*} [Field F]

def thirdTwoTorsionX (W : WeierstrassCurve F) (x₁ x₂ : F) : F := -W.b₂ / 4 - x₁ - x₂

def legendreLambda (W : WeierstrassCurve F) (x₁ x₂ : F) : F :=
  (W.thirdTwoTorsionX x₁ x₂ - x₁) / (x₂ - x₁)

def legendreVariableChange (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) : VariableChange F :=
  ⟨Units.mk0 w hw, x₁, -W.a₁ / 2, -(W.a₃ + x₁ * W.a₁) / 2⟩

@[simp] theorem legendreVariableChange_u (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    ((W.legendreVariableChange x₁ w hw).u : F) = w := rfl

@[simp] theorem legendreVariableChange_r (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).r = x₁ := rfl

@[simp] theorem legendreVariableChange_s (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).s = -W.a₁ / 2 := rfl

@[simp] theorem legendreVariableChange_t (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).t = -(W.a₃ + x₁ * W.a₁) / 2 := rfl

theorem legendreLambda_def (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.legendreLambda x₁ x₂ = (-W.b₂ / 4 - x₁ - x₂ - x₁) / (x₂ - x₁) := rfl

theorem thirdTwoTorsionX_legendreCurve (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).thirdTwoTorsionX 0 1 = t := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  simp only [thirdTwoTorsionX, legendreCurve, WeierstrassCurve.b₂]
  field_simp
  ring

theorem legendreLambda_legendreCurve (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).legendreLambda 0 1 = t := by
  rw [legendreLambda, thirdTwoTorsionX_legendreCurve h2]; simp

theorem thirdTwoTorsionX_variableChange (h2 : (2 : F) ≠ 0) (C : VariableChange F)
    (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.thirdTwoTorsionX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
      = (C.u : F) ^ 2 * (C • W).thirdTwoTorsionX x₁ x₂ + C.r := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [thirdTwoTorsionX, variableChange_b₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem legendreLambda_variableChange (h2 : (2 : F) ≠ 0) (C : VariableChange F)
    (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.legendreLambda ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).legendreLambda x₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hu2 : (C.u : F) ^ 2 ≠ 0 := pow_ne_zero 2 hu
  rw [legendreLambda, legendreLambda, thirdTwoTorsionX_variableChange h2]
  rw [show (C.u : F) ^ 2 * (C • W).thirdTwoTorsionX x₁ x₂ + C.r - ((C.u : F) ^ 2 * x₁ + C.r)
      = (C.u : F) ^ 2 * ((C • W).thirdTwoTorsionX x₁ x₂ - x₁) by ring,
    show (C.u : F) ^ 2 * x₂ + C.r - ((C.u : F) ^ 2 * x₁ + C.r) = (C.u : F) ^ 2 * (x₂ - x₁) by ring,
    mul_div_mul_left _ _ hu2]

theorem thirdTwoTorsionX_map {K : Type*} [Field K] (φ : F →+* K) (W : WeierstrassCurve F)
    (x₁ x₂ : F) :
    (W.map φ).thirdTwoTorsionX (φ x₁) (φ x₂) = φ (W.thirdTwoTorsionX x₁ x₂) := by
  simp [thirdTwoTorsionX, WeierstrassCurve.map_b₂, map_div₀, map_sub, map_neg, map_ofNat]

theorem legendreLambda_map {K : Type*} [Field K] (φ : F →+* K) (W : WeierstrassCurve F)
    (x₁ x₂ : F) :
    (W.map φ).legendreLambda (φ x₁) (φ x₂) = φ (W.legendreLambda x₁ x₂) := by
  rw [legendreLambda, legendreLambda, thirdTwoTorsionX_map, map_div₀, map_sub, map_sub]

end WeierstrassCurve
