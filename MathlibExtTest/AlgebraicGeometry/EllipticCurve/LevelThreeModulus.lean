/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.LevelThreeModulus

open WeierstrassCurve

example {R : Type*} [CommRing R] (α β : R) : (deuringCurve α β).Δ = β ^ 3 * (α ^ 3 - 27 * β) :=
  deuringCurve_Δ α β

example {F : Type*} [Field F] {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeModulus 0 0 ν = τ :=
  levelThreeModulus_deuringCurve hν

example {F : Type*} [Field F] {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeAbscissa 0 0 ν = ν :=
  levelThreeAbscissa_deuringCurve hν

example {F : Type*} [Field F] {τ ν : F} (hν : ν ≠ 0) (η : F) :
    (deuringCurve τ ν).levelThreeOrdinate 0 0 ν η = η :=
  levelThreeOrdinate_deuringCurve hν η

/-! Concrete values: `y² + xy + 2y = x³ + 3x² + 3x + 1` is `deuringCurve 1 1` translated by
`x ↦ x + 1`, with its flex at `(-1, 0)`. -/

private abbrev translatedDeuring : WeierstrassCurve ℚ := ⟨1, 3, 2, 3, 1⟩

private theorem translatedDeuring_eq :
    (⟨1, 1, 0, 0⟩ : VariableChange ℚ) • deuringCurve (1 : ℚ) 1 = translatedDeuring := by
  ext <;> norm_num [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]

example : translatedDeuring.levelThreeModulus (-1) 0 1 = 2 := by
  rw [levelThreeModulus_eq_div]
  norm_num [deuringA₃_def, tangentSlopeNum_def]

example : translatedDeuring.levelThreeAbscissa (-1) 0 1 = 8 := by
  rw [levelThreeAbscissa_eq_div]
  norm_num [deuringA₃_def]

-- Normalization of the flex `(-1, 0)` with the second abscissa `1`: the scaling is
-- `u = 1 / 2` and the Deuring form is `deuringCurve 2 8`.
example :
    translatedDeuring.deuringVariableChange (-1) 0 (Units.mk0 (1 / 2) (by norm_num)) •
      translatedDeuring = deuringCurve 2 8 := by
  have heq : translatedDeuring.toAffine.Equation (-1) 0 := by
    rw [Affine.equation_iff]; norm_num
  have hΨ : translatedDeuring.deuringA₃ (-1) 0 ≠ 0 := by norm_num [deuringA₃_def]
  have hflex : translatedDeuring.flexForm (-1) 0 = 0 := by
    norm_num [flexForm_def, tangentSlopeNum_def, deuringA₃_def]
  rw [deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus heq hΨ hflex (x₂ := 1)
    (by norm_num) _ (by norm_num [deuringA₃_def])]
  congr 1
  · rw [levelThreeModulus_eq_div]; norm_num [deuringA₃_def, tangentSlopeNum_def]
  · rw [levelThreeAbscissa_eq_div]; norm_num [deuringA₃_def]

-- The variable-change law moves the computation to the Deuring side: at the images
-- `(0, 0)` and `2` of `(-1, 0)` and `1`, the modulus of `deuringCurve 1 1` is also `2`.
example : translatedDeuring.levelThreeModulus (-1) 0 1 =
    (deuringCurve (1 : ℚ) 1).levelThreeModulus 0 0 2 := by
  have h := levelThreeModulus_variableChange (W := deuringCurve (1 : ℚ) 1) ⟨1, 1, 0, 0⟩ (-1) 0 1
  rw [translatedDeuring_eq] at h
  rw [← h]
  norm_num

example : (deuringCurve (1 : ℚ) 1).levelThreeModulus 0 0 2 = 2 := by
  rw [levelThreeModulus_eq_div]
  norm_num [deuringA₃_def, tangentSlopeNum_def]

-- Undoing any variable change `C` recovers the Deuring modulus and ordinate.
example {F : Type*} [Field F] (C : VariableChange F) {τ ν : F} (hν : ν ≠ 0) :
    (C⁻¹ • deuringCurve τ ν).levelThreeModulus ((C.u : F) ^ 2 * 0 + C.r)
      ((C.u : F) ^ 3 * 0 + (C.u : F) ^ 2 * C.s * 0 + C.t) ((C.u : F) ^ 2 * ν + C.r) = τ := by
  rw [levelThreeModulus_variableChange, smul_inv_smul, levelThreeModulus_deuringCurve hν]

example {F : Type*} [Field F] (C : VariableChange F) {τ ν : F} (hν : ν ≠ 0) (η : F) :
    (C⁻¹ • deuringCurve τ ν).levelThreeOrdinate ((C.u : F) ^ 2 * 0 + C.r)
      ((C.u : F) ^ 3 * 0 + (C.u : F) ^ 2 * C.s * 0 + C.t) ((C.u : F) ^ 2 * ν + C.r)
      ((C.u : F) ^ 3 * η + (C.u : F) ^ 2 * C.s * ν + C.t) = η := by
  rw [levelThreeOrdinate_variableChange, smul_inv_smul, levelThreeOrdinate_deuringCurve hν]

/-! Base change. -/

-- Reduction modulo `5` along a non-injective ring map, where the denominator `1` is a unit.
example :
    ((deuringCurve (2 : ℤ) 1).map (Int.castRingHom (ZMod 5))).levelThreeModulus 0 0 3 = 1 := by
  have hu : IsUnit ((deuringCurve (2 : ℤ) 1).deuringA₃ 0 0) := by simp [deuringA₃_def]
  have h := levelThreeModulus_map_of_isUnit (Int.castRingHom (ZMod 5)) hu 3
  simp only [map_zero, map_ofNat] at h
  rw [h, levelThreeModulus_def, deuringA₁_def, tangentSlope_def]
  simp [deuringA₃_def, tangentSlopeNum_def]
  decide

-- Along a field homomorphism no unit hypothesis is needed.
example {K : Type*} [Field K] (φ : ℚ →+* K) :
    (translatedDeuring.map φ).levelThreeModulus (-1) 0 1 = 2 := by
  have h := levelThreeModulus_map φ (W := translatedDeuring) (-1) 0 1
  simp only [map_neg, map_one, map_zero] at h
  rw [h, levelThreeModulus_eq_div]
  norm_num [deuringA₃_def, tangentSlopeNum_def]

/-! Zero denominators: the totalized definitions vanish. -/

example {F : Type*} [Field F] (τ x₂ y₂ : F) :
    (deuringCurve τ 0).tangentSlope 0 0 = 0 ∧ (deuringCurve τ 0).deuringA₁ 0 0 = τ ∧
      (deuringCurve τ 0).levelThreeModulus 0 0 x₂ = 0 ∧
      (deuringCurve τ 0).levelThreeAbscissa 0 0 x₂ = 0 ∧
      (deuringCurve τ 0).levelThreeOrdinate 0 0 x₂ y₂ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [tangentSlope_def, deuringA₁_def, levelThreeModulus_def, levelThreeAbscissa_def,
      levelThreeOrdinate_def, deuringA₃_deuringCurve_zero]

-- So `levelThreeModulus_deuringCurve` needs `ν ≠ 0`: here `τ = 1` but the value is `0`.
example : (deuringCurve (1 : ℚ) 0).levelThreeModulus 0 0 0 = 0 := by
  simp [levelThreeModulus_def, deuringA₃_deuringCurve_zero]

-- Equal abscissas: no scaling sends the second abscissa to `β`, and the three level-three
-- formulas are all `0`.
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₁ y₁ y₂ : R) :
    W.levelThreeModulus x₁ y₁ x₁ = 0 ∧ W.levelThreeAbscissa x₁ y₁ x₁ = 0 ∧
      W.levelThreeOrdinate x₁ y₁ x₁ y₂ = 0 := by
  simp [levelThreeModulus_def, levelThreeAbscissa_def, levelThreeOrdinate_def]

private abbrev cubicMinusX : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

private abbrev shear : VariableChange ℚ := ⟨1, 0, 1, 0⟩

-- The variable-change laws of `tangentSlope` and `deuringA₁` need a nonzero denominator: on
-- `y² = x³ - x` at `(0, 0)`, the variable change `(1, 0, 1, 0)` fixes the point and leaves the
-- denominator `0`, and the conclusions of `tangentSlope_variableChange` and
-- `deuringA₁_variableChange` fail there (`0 ≠ 0 + 1` and `0 ≠ 2`).
example : (shear • cubicMinusX).deuringA₃ 0 0 = 0 ∧
    cubicMinusX.tangentSlope ((shear.u : ℚ) ^ 2 * 0 + shear.r)
        ((shear.u : ℚ) ^ 3 * 0 + (shear.u : ℚ) ^ 2 * shear.s * 0 + shear.t) ≠
      (shear.u : ℚ) * (shear • cubicMinusX).tangentSlope 0 0 + shear.s ∧
    cubicMinusX.deuringA₁ ((shear.u : ℚ) ^ 2 * 0 + shear.r)
        ((shear.u : ℚ) ^ 3 * 0 + (shear.u : ℚ) ^ 2 * shear.s * 0 + shear.t) ≠
      (shear.u : ℚ) * (shear • cubicMinusX).deuringA₁ 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [deuringA₃_def, deuringA₁_def, tangentSlope_eq_div, tangentSlopeNum_def,
      variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]

-- Over `ℤ` the denominator `2` is not a unit, so the modulus is `0`; over `ℚ` it is `2`. This is
-- why `levelThreeModulus_map_of_isUnit` needs its unit hypothesis.
example : (deuringCurve (1 : ℤ) 2).levelThreeModulus 0 0 4 = 0 := by
  have h : ¬IsUnit ((deuringCurve (1 : ℤ) 2).deuringA₃ 0 0) := by
    simp [deuringA₃_def, Int.isUnit_iff]
  rw [levelThreeModulus_def, Ring.inverse_non_unit _ h, mul_zero]

example : ((deuringCurve (1 : ℤ) 2).map (Int.castRingHom ℚ)).levelThreeModulus 0 0 4 = 2 := by
  rw [deuringCurve_map, levelThreeModulus_eq_div]
  norm_num [deuringA₃_def, tangentSlopeNum_def]

example : (deuringCurve (0 : ℚ) (-1)).Δ = -27 := by
  rw [deuringCurve_Δ_of_levelThree_rel (by norm_num)]
  norm_num
