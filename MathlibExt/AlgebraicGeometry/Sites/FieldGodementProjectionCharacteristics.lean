/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementProjectionData
public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementProjectionTensorNaturality

/-! # Characteristic equations for the original stored field product projections -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

/-- The actual tensor source stalk on the two original family sheaves. -/
def fieldGodementSourceStalkTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    AddCommGrpCat.{max u w} :=
  AddCommGrpCat.of
    (((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementFamilySheaf.{u, w} k M) ⊗[ℤ]
      ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
          (fieldGodementFamilySheaf.{u, w} k N))

/-- The actual tensor target stalk on the two original point sheaves. -/
def fieldGodementTargetStalkTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    AddCommGrpCat.{max u w} :=
  AddCommGrpCat.of
    (((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementPointSheaf.{u, w} k (M default)) ⊗[ℤ]
      ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
          (fieldGodementPointSheaf.{u, w} k (N default)))

/-- The original source stalk tensor-germ arrow. -/
def fieldGodementSourceStalkTensorMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementFamilyTensorSheaf.{u, w} k M N) ⟶
      fieldGodementSourceStalkTensor.{u, w} k M N :=
  (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) (fieldGodementCanonicalPoint.{u, w} k)
    (fieldGodementFamilySheaf.{u, w} k M) (fieldGodementFamilySheaf.{u, w} k N)).hom

/-- The original target stalk tensor-germ arrow. -/
def fieldGodementTargetStalkTensorMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementPointTensorSheaf.{u, w} k M N) ⟶
      fieldGodementTargetStalkTensor.{u, w} k M N :=
  (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) (fieldGodementCanonicalPoint.{u, w} k)
    (fieldGodementPointSheaf.{u, w} k (M default))
        (fieldGodementPointSheaf.{u, w} k (N default))).hom

/-- Tensor the actual projected stalk arrows. -/
def fieldGodementProjectedStalkTensorMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementSourceStalkTensor.{u, w} k M N ⟶ fieldGodementTargetStalkTensor.{u, w} k M N :=
  let L := (fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})
  AddCommGrpCat.ofHom (TensorProduct.map
    (L.map (fieldGodementFamilyProjection.{u, w} k M)).hom.toIntLinearMap
    (L.map (fieldGodementFamilyProjection.{u, w} k N)).hom.toIntLinearMap).toAddMonoidHom

/-- Tensor the original target point counits. -/
def fieldGodementPointCounitTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementTargetStalkTensor.{u, w} k M N ⟶ AddCommGrpCat.of (M default ⊗[ℤ] N default) :=
  let adj := (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w})
  AddCommGrpCat.ofHom (TensorProduct.map
    (adj.counit.app (M default)).hom.toIntLinearMap
    (adj.counit.app (N default)).hom.toIntLinearMap).toAddMonoidHom

/-- Tensor the actual source family counit components. -/
def fieldGodementFamilyCounitTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementSourceStalkTensor.{u, w} k M N ⟶ AddCommGrpCat.of (M default ⊗[ℤ] N default) :=
  let adj := smallEtaleGodementAdjunction.{u, w} (Spec (.of k))
  AddCommGrpCat.ofHom (TensorProduct.map
    ((adj.counit.app M) default).hom.toIntLinearMap
    ((adj.counit.app N) default).hom.toIntLinearMap).toAddMonoidHom

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual source-family projected pairing has the original counit characteristic in the stored
tensor objects. -/
theorem fieldGodementProjectedPairing_characteristic
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).map
        (fieldGodementFamilyProjectedPairing.{u, w} k M N) ≫
        (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.counit.app
          (AddCommGrpCat.of (M default ⊗[ℤ] N default)) =
      fieldGodementSourceStalkTensorMap.{u, w} k M N ≫
          fieldGodementFamilyCounitTensor.{u, w} k M N :=
  fieldGodementSkyscraperPairing_projection_counit.{u, w} k M N

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual target point pairing has the original counit characteristic in the stored tensor
objects. -/
theorem fieldGodementPointPairing_characteristic
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).map
        (fieldGodementPointPairing.{u, w} k M N) ≫
        (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.counit.app
          (AddCommGrpCat.of (M default ⊗[ℤ] N default)) =
      fieldGodementTargetStalkTensorMap.{u, w} k M N ≫
          fieldGodementPointCounitTensor.{u, w} k M N :=
  fieldCanonicalPointSkyscraperTensorPairing_counit.{u, w} k (M default) (N default)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual stored tensor-germ arrows are natural for the actual family product projections. -/
theorem fieldGodementStoredProjectionTensor_naturality
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).map
        (fieldGodementTensorProjectionMap.{u, w} k M N) ≫
        fieldGodementTargetStalkTensorMap.{u, w} k M N =
      fieldGodementSourceStalkTensorMap.{u, w} k M N ≫
          fieldGodementProjectedStalkTensorMap.{u, w} k M N :=
  fieldGodementProjectionTensor_naturality.{u, w} k M N

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual stored point counit tensor after projection equals the original family counit
tensor. -/
theorem fieldGodementStoredCounitTensor_comp
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementProjectedStalkTensorMap.{u, w} k M N ≫
        fieldGodementPointCounitTensor.{u, w} k M N =
      fieldGodementFamilyCounitTensor.{u, w} k M N :=
  fieldGodementProjectedCounitTensor.{u, w} k M N

end AlgebraicGeometry.Scheme.DerivedSections
