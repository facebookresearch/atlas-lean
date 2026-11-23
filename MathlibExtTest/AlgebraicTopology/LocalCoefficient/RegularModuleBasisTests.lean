/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis

/-!
# Actual integral coproduct, native generator, and group-ring consumers

Two distinct summands carry positive and negative integers through both maps.
The native generator comparison keeps its original base simplex. Group-ring
transport checks right multiplication by a positive label for the inverse-End
path and by the inverse label for the positive-End path.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits SSet SSet.KanComplex
open scoped Simplicial

universe u

namespace MathlibExtTest.RegularModuleBasis

/-- The public module owner supplies its actual coproduct instance at import. -/
theorem fresh_integral_module_coproduct_instance : HasCoproducts.{0} (ModuleCat.{0} ℤ) := by
  infer_instance

/-- The forward map keeps two original summands and their signed integer coefficients. -/
theorem integral_coproduct_forward_two_signed_summands :
    let I := Fin 3
    let s := fun _ : I => ModuleCat.of ℤ (ULift.{0} ℤ)
    let v := Sigma.ι s 0 (ULift.up (2 : ℤ)) - Sigma.ι s 2 (ULift.up (3 : ℤ))
    (integralPathModuleBasisIso I).hom v =
      (2 : ℤ) • FreeAbelianGroup.of (0 : I) - (3 : ℤ) • FreeAbelianGroup.of (2 : I) := by
  let I := Fin 3
  let s := fun _ : I => ModuleCat.of ℤ (ULift.{0} ℤ)
  let e := integralPathModuleBasisIso I
  let a := Sigma.ι s 0 (ULift.up (2 : ℤ))
  let b := Sigma.ι s 2 (ULift.up (3 : ℤ))
  exact (e.hom.hom.map_sub a b).trans
    (congrArg₂ (fun a b => a - b)
      (integralPathModuleBasisIso_hom_ι_apply I 0 (ULift.up (2 : ℤ)))
      (integralPathModuleBasisIso_hom_ι_apply I 2 (ULift.up (3 : ℤ))))

/-- The inverse returns the same two literal summand inclusions with both integers. -/
theorem integral_coproduct_inverse_two_signed_summands :
    let I := Fin 3
    let s := fun _ : I => ModuleCat.of ℤ (ULift.{0} ℤ)
    (integralPathModuleBasisIso I).inv
        ((2 : ℤ) • FreeAbelianGroup.of (0 : I) - (3 : ℤ) • FreeAbelianGroup.of (2 : I)) =
      Sigma.ι s 0 (ULift.up (2 : ℤ)) - Sigma.ι s 2 (ULift.up (3 : ℤ)) := by
  let I := Fin 3
  let e := integralPathModuleBasisIso I
  exact (e.inv.hom.map_sub ((2 : ℤ) • FreeAbelianGroup.of (0 : I))
      ((3 : ℤ) • FreeAbelianGroup.of (2 : I))).trans
    (congrArg₂ (fun a b => a - b)
      (integralPathModuleBasisIso_inv_zsmul I 0 (2 : ℤ))
      (integralPathModuleBasisIso_inv_zsmul I 2 (3 : ℤ)))

/-- Both actual maps cancel on a multi-summand coproduct element and its free path vector. -/
theorem integral_coproduct_both_signed_roundtrips :
    let I := Fin 3
    let s := fun _ : I => ModuleCat.of ℤ (ULift.{0} ℤ)
    let e := integralPathModuleBasisIso I
    let v := Sigma.ι s 0 (ULift.up (2 : ℤ)) - Sigma.ι s 2 (ULift.up (3 : ℤ))
    let t := (2 : ℤ) • FreeAbelianGroup.of (0 : I) - (3 : ℤ) • FreeAbelianGroup.of (2 : I)
    e.inv (e.hom v) = v ∧ e.hom (e.inv t) = t := by
  let I := Fin 3
  let s := fun _ : I => ModuleCat.of ℤ (ULift.{0} ℤ)
  let e := integralPathModuleBasisIso I
  let v := Sigma.ι s 0 (ULift.up (2 : ℤ)) - Sigma.ι s 2 (ULift.up (3 : ℤ))
  let t := (2 : ℤ) • FreeAbelianGroup.of (0 : I) - (3 : ℤ) • FreeAbelianGroup.of (2 : I)
  constructor
  · exact congrArg (fun f : (∐ s) ⟶ (∐ s) => f v) e.hom_inv_id
  · exact congrArg (fun f : ModuleCat.of ℤ (FreeAbelianGroup I) ⟶
      ModuleCat.of ℤ (FreeAbelianGroup I) => f t) e.inv_hom_id

/-- The native comparison returns every original pair and preserves its actual base simplex. -/
theorem native_generator_original_coordinate_roundtrip
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) (g : nativeCoverSimplexPathGenerators X x n) :
    let e := nativeCoverSimplexPathGeneratorsEquiv X x n
    e.symm (e g) = g ∧
      (nativeCoverProjection X x).app (Opposite.op ⦋n⦌) (e g) =
        (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)) g.1 := by
  exact ⟨nativeCoverSimplexPathGeneratorsEquiv_left_inv X x n g,
    nativeCoverSimplexPathGeneratorsEquiv_projection X x n g⟩

/-- The actual group-ring maps keep a negative integer and the original inverse-End label. -/
theorem native_group_ring_signed_basis_two_directions
    (Y : SSet.{u}) [SSet.KanComplex Y] (y : Y _⦋0⦌) (a : π 1 Y y) :
    let ψ := piOneMulEquivFundamentalGroupoidEnd y
    let e := nativeRegularBasedGroupRingIso y
    let γ := ((ψ a)⁻¹).asHom
    e.hom ((-3 : ℤ) • FreeAbelianGroup.of γ) = MonoidAlgebra.single a (-3 : ℤ) ∧
      e.inv (MonoidAlgebra.single a (-3 : ℤ)) = (-3 : ℤ) • FreeAbelianGroup.of γ := by
  let ψ := piOneMulEquivFundamentalGroupoidEnd y
  let e := nativeRegularBasedGroupRingIso y
  let γ := ((ψ a)⁻¹).asHom
  have hIndex : (nativeRegularBasedGroupRingIndexEquiv y) γ = a :=
    (nativeRegularBasedGroupRingIndexEquiv y).apply_symm_apply a
  constructor
  · exact (nativeRegularBasedGroupRingIso_hom_zsmul y γ (-3 : ℤ)).trans
      (congrArg (fun b => MonoidAlgebra.single b (-3 : ℤ)) hIndex)
  · exact nativeRegularBasedGroupRingIso_inv_single y a (-3 : ℤ)

/-- The inverse-End transport multiplies on the right by the positive loop label. -/
theorem native_group_ring_inverse_path_right_product
    (Y : SSet.{u}) [SSet.KanComplex Y] (y : Y _⦋0⦌) (a b : π 1 Y y) :
    let ψ := piOneMulEquivFundamentalGroupoidEnd y
    let e := nativeRegularBasedGroupRingIso y
    e.hom ((regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).map
        ((ψ b)⁻¹).asHom (e.inv (MonoidAlgebra.single a (-3 : ℤ)))) =
      MonoidAlgebra.single (a * b) (-3 : ℤ) := by
  let ψ := piOneMulEquivFundamentalGroupoidEnd y
  let e := nativeRegularBasedGroupRingIso y
  let t := MonoidAlgebra.single a (-3 : ℤ)
  have hRound : e.hom (e.inv t) = t :=
    congrArg (fun f : ModuleCat.of ℤ (MonoidAlgebra ℤ (π 1 Y y)) ⟶
      ModuleCat.of ℤ (MonoidAlgebra ℤ (π 1 Y y)) => f t) e.inv_hom_id
  have hTransport := nativeRegularBasedGroupRingIso_postcomp_inverse y b (e.inv t)
  exact hTransport.trans
    ((congrArg (fun r => r * MonoidAlgebra.single b (1 : ℤ)) hRound).trans
      ((MonoidAlgebra.single_mul_single a b (-3 : ℤ) (1 : ℤ)).trans
        (congrArg (MonoidAlgebra.single (a * b)) (mul_one (-3 : ℤ)))))

/-- The positive-End transport uses the inverse label, with the same right multiplication. -/
theorem native_group_ring_positive_path_right_inverse_product
    (Y : SSet.{u}) [SSet.KanComplex Y] (y : Y _⦋0⦌) (a b : π 1 Y y) :
    let ψ := piOneMulEquivFundamentalGroupoidEnd y
    let e := nativeRegularBasedGroupRingIso y
    e.hom ((regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y)).map
        (ψ b).asHom (e.inv (MonoidAlgebra.single a (-3 : ℤ)))) =
      MonoidAlgebra.single (a * b⁻¹) (-3 : ℤ) := by
  let ψ := piOneMulEquivFundamentalGroupoidEnd y
  let e := nativeRegularBasedGroupRingIso y
  let t := MonoidAlgebra.single a (-3 : ℤ)
  have hRound : e.hom (e.inv t) = t :=
    congrArg (fun f : ModuleCat.of ℤ (MonoidAlgebra ℤ (π 1 Y y)) ⟶
      ModuleCat.of ℤ (MonoidAlgebra ℤ (π 1 Y y)) => f t) e.inv_hom_id
  have hTransport := nativeRegularBasedGroupRingIso_postcomp_positive y b (e.inv t)
  exact hTransport.trans
    ((congrArg (fun r => r * MonoidAlgebra.single b⁻¹ (1 : ℤ)) hRound).trans
      ((MonoidAlgebra.single_mul_single a b⁻¹ (-3 : ℤ) (1 : ℤ)).trans
        (congrArg (MonoidAlgebra.single (a * b⁻¹)) (mul_one (-3 : ℤ)))))

end MathlibExtTest.RegularModuleBasis

end
