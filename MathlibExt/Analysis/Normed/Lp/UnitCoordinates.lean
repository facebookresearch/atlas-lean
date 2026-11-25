/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Unit-coordinate isometries of square-summable families

Let I be any index type and β : I → ℂ satisfy ‖β_i‖ = 1 for every i.
Coordinate multiplication x_i ↦ β_i x_i is a continuous complex-linear map
on ℓ²(I,ℂ), preserves its norm, and has inverse x_i ↦ β_i⁻¹ x_i.
It therefore defines a linear isometric equivalence. Empty, finite and
infinite index types are allowed.
-/

@[expose] public section
noncomputable section
namespace MathlibExt.Analysis.Normed.Lp
open scoped ENNReal
universe u

/-- For any index type I and β : I → ℂ with ‖β_i‖ = 1 for all i,
coordinate multiplication x_i ↦ β_i x_i defines a continuous complex-linear
map on the square-summable space ℓ²(I,ℂ). -/
def unitCoordinateMap {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1) :
    lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  lp.mapCLM 2 (fun i => beta i • ContinuousLinearMap.id ℂ ℂ) (by norm_num : (0 : ℝ) ≤ 1)
    (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using (hunit i).le)

/-- Let I be any index type and β : I → ℂ have norm-one values.
For x ∈ ℓ²(I,ℂ) and i : I, (unitCoordinateMap β x)_i = β_i x_i. -/
theorem unitCoordinateMap_apply {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1)
    (x : lp (fun _ : I => ℂ) 2) (i : I) : unitCoordinateMap beta hunit x i = beta i * x i := rfl

/-- For any index type I and β : I → ℂ with ‖β_i‖ = 1 for every i,
each β_i is nonzero. -/
theorem unitCoordinate_ne_zero {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1) (i : I) :
    beta i ≠ 0 := by
  intro hz
  have h := hunit i
  rw [hz, norm_zero] at h
  exact zero_ne_one h

/-- For any index type I and β : I → ℂ with ‖β_i‖ = 1 for every i,
the reciprocal family also satisfies ‖β_i⁻¹‖ = 1 for every i. -/
theorem inverseUnitCoordinates {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1) :
    ∀ i, ‖(beta i)⁻¹‖ = 1 := fun i => by rw [norm_inv, hunit i, inv_one]

/-- For any index type I and norm-one family β : I → ℂ, multiplication
by the reciprocal coordinates after multiplication by β returns every
x ∈ ℓ²(I,ℂ). -/
theorem unitCoordinateMap_left_inv {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1)
    (x : lp (fun _ : I => ℂ) 2) :
    unitCoordinateMap (fun i => (beta i)⁻¹) (inverseUnitCoordinates beta hunit)
      (unitCoordinateMap beta hunit x) = x := by
  apply lp.ext
  apply funext
  intro i
  rw [unitCoordinateMap_apply, unitCoordinateMap_apply, ← mul_assoc,
    inv_mul_cancel₀ (unitCoordinate_ne_zero beta hunit i), one_mul]

/-- For any index type I and norm-one family β : I → ℂ, multiplication
by β after multiplication by its reciprocal coordinates returns every
x ∈ ℓ²(I,ℂ). -/
theorem unitCoordinateMap_right_inv {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1)
    (x : lp (fun _ : I => ℂ) 2) :
    unitCoordinateMap beta hunit
      (unitCoordinateMap (fun i => (beta i)⁻¹) (inverseUnitCoordinates beta hunit) x) = x := by
  apply lp.ext
  apply funext
  intro i
  rw [unitCoordinateMap_apply, unitCoordinateMap_apply, ← mul_assoc,
    mul_inv_cancel₀ (unitCoordinate_ne_zero beta hunit i), one_mul]

/-- For any index type I, β : I → ℂ with ‖β_i‖ = 1, and x ∈ ℓ²(I,ℂ),
coordinate multiplication by β preserves the full square-summable norm. -/
theorem unitCoordinateMap_norm {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1)
    (x : lp (fun _ : I => ℂ) 2) : ‖unitCoordinateMap beta hunit x‖ = ‖x‖ := by
  have he : ∀ i, ‖unitCoordinateMap beta hunit x i‖ = ‖x i‖ := by
    intro i
    rw [unitCoordinateMap_apply, norm_mul, hunit i, one_mul]
  exact le_antisymm
    (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun i => (he i).le))
    (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun i => (he i).ge))

/-- For any index type I and β : I → ℂ with ‖β_i‖ = 1 for all i,
coordinate multiplication by β is a complex-linear isometric equivalence
of ℓ²(I,ℂ), with inverse multiplication by the reciprocal family. -/
def unitCoordinateEquiv {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1) :
    lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 2 where
  toFun := unitCoordinateMap beta hunit
  invFun := unitCoordinateMap (fun i => (beta i)⁻¹) (inverseUnitCoordinates beta hunit)
  left_inv := unitCoordinateMap_left_inv beta hunit
  right_inv := unitCoordinateMap_right_inv beta hunit
  map_add' := (unitCoordinateMap beta hunit).map_add
  map_smul' := (unitCoordinateMap beta hunit).map_smul
  norm_map' := unitCoordinateMap_norm beta hunit

/-- For any index type I, norm-one family β : I → ℂ, x ∈ ℓ²(I,ℂ)
and i : I, the forward isometric equivalence has coordinate β_i x_i. -/
theorem unitCoordinateEquiv_apply {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1)
    (x : lp (fun _ : I => ℂ) 2) (i : I) : unitCoordinateEquiv beta hunit x i = beta i * x i := rfl

/-- For any index type I, norm-one family β : I → ℂ, x ∈ ℓ²(I,ℂ)
and i : I, the inverse isometric equivalence has coordinate β_i⁻¹ x_i. -/
theorem unitCoordinateEquiv_symm_apply {I : Type u} (beta : I → ℂ) (hunit : ∀ i, ‖beta i‖ = 1)
    (x : lp (fun _ : I => ℂ) 2) (i : I) : (unitCoordinateEquiv beta hunit).symm x i = (beta i)⁻¹ * x i := rfl

end MathlibExt.Analysis.Normed.Lp
