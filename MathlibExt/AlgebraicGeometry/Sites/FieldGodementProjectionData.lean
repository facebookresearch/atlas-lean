/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementTensorProjection
public import MathlibExt.CategoryTheory.Adjunction.ComparisonMonadIso

/-! # Stored actual field Godement projection objects and maps -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

/-- The actual skyscraper product on an original field-point coefficient family. -/
def fieldGodementFamilySheaf (M : Spec (.of k) → AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  (smallEtaleGodementSkyscrapers.{u, w} (Spec (.of k))).obj M

/-- The actual original canonical point skyscraper on an additive coefficient group. -/
def fieldGodementPointSheaf (M : AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafFunctor.obj M

/-- The actual singleton product projection as a map between the stored original sheaves. -/
def fieldGodementFamilyProjection (M : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementFamilySheaf.{u, w} k M ⟶ fieldGodementPointSheaf.{u, w} k (M default) :=
  Pi.π (fun y : Spec (.of k) =>
    (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) y)).skyscraperSheafFunctor.obj
          (M y)) default

/-- The source integer tensor sheaf on the actual two family products. -/
def fieldGodementFamilyTensorSheaf (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  smallEtaleTensorSheaf.{u, w} (Spec (.of k))
    (fieldGodementFamilySheaf.{u, w} k M) (fieldGodementFamilySheaf.{u, w} k N)

/-- The target integer tensor sheaf on the actual two point skyscrapers. -/
def fieldGodementPointTensorSheaf (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  smallEtaleTensorSheaf.{u, w} (Spec (.of k))
    (fieldGodementPointSheaf.{u, w} k (M default)) (fieldGodementPointSheaf.{u, w} k (N default))

/-- Tensor the actual two family product projections. -/
def fieldGodementTensorProjectionMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementFamilyTensorSheaf.{u, w} k M N ⟶ fieldGodementPointTensorSheaf.{u, w} k M N :=
  smallEtaleTensorSheafMap.{u, w} (Spec (.of k))
    (fieldGodementFamilyProjection.{u, w} k M) (fieldGodementFamilyProjection.{u, w} k N)

/-- The original family pairing followed by its actual singleton tensor-family projection. -/
def fieldGodementFamilyProjectedPairing (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementFamilyTensorSheaf.{u, w} k M N ⟶
      fieldGodementPointSheaf.{u, w} k (AddCommGrpCat.of (M default ⊗[ℤ] N default)) :=
  smallEtaleGodementSkyscraperPairing.{u, w} (Spec (.of k)) M N ≫
    fieldGodementFamilyProjection.{u, w} k
        (smallEtaleGodementFamilyTensor.{u, w} (Spec (.of k)) M N)

/-- The actual target canonical point pairing on the same stored tensor sheaf. -/
def fieldGodementPointPairing (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementPointTensorSheaf.{u, w} k M N ⟶
      fieldGodementPointSheaf.{u, w} k (AddCommGrpCat.of (M default ⊗[ℤ] N default)) :=
  fieldCanonicalPointSkyscraperTensorPairing.{u, w} k (M default) (N default)

end AlgebraicGeometry.Scheme.DerivedSections
