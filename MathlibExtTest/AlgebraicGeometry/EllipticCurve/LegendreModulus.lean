/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.LegendreModulus

open WeierstrassCurve

example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).legendreLambda 0 1 = t :=
  legendreLambda_legendreCurve h2 t

example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).thirdTwoTorsionX 0 1 = t :=
  thirdTwoTorsionX_legendreCurve h2 t

-- `y² = x³ - x = x(x - 1)(x + 1)`: the roots `0` and `1` leave the third root `-1`.
example : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).thirdTwoTorsionX 0 1 = -1 := by
  norm_num [thirdTwoTorsionX, b₂]

example : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).legendreLambda 0 1 = -1 := by
  norm_num [legendreLambda_def, b₂]

-- Equal abscissas: the division by `x₂ - x₁ = 0` is totalized to `0`.
example {F : Type*} [Field F] (W : WeierstrassCurve F) (x : F) : W.legendreLambda x x = 0 := by
  simp [legendreLambda]

-- When `2 ≠ 0`, the Legendre variable change completes the square: `a₁ = a₃ = 0` afterwards.
example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (W : WeierstrassCurve F) (x₁ w : F)
    (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw • W).a₁ = 0 ∧
      (W.legendreVariableChange x₁ w hw • W).a₃ = 0 := by
  constructor
  · rw [variableChange_a₁, Units.val_inv_eq_inv_val, legendreVariableChange_u,
      legendreVariableChange_s]
    field_simp
    ring
  · rw [variableChange_a₃, Units.val_inv_eq_inv_val, legendreVariableChange_u,
      legendreVariableChange_r, legendreVariableChange_t]
    field_simp
    ring

-- Undoing any variable change `C` recovers the Legendre parameter `t`.
example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (C : VariableChange F) (t : F) :
    (C⁻¹ • legendreCurve t).legendreLambda ((C.u : F) ^ 2 * 0 + C.r) ((C.u : F) ^ 2 * 1 + C.r) =
      t := by
  rw [legendreLambda_variableChange h2, smul_inv_smul, legendreLambda_legendreCurve h2]

-- Base change along a field homomorphism.
example {K : Type*} [Field K] (φ : ℚ →+* K) :
    ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).map φ).legendreLambda 0 1 = -1 := by
  have h := legendreLambda_map φ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ) 0 1
  simp only [map_zero, map_one] at h
  rw [h]
  norm_num [legendreLambda_def, b₂]
