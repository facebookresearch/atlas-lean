/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementProjectionCharacteristics
public import MathlibExt.CategoryTheory.Adjunction.ComparisonMonadIso

/-! # The original binary pairing under its actual product projections -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency.types false in
/-- The original Godement family pairing equals the actual point pairing after the two genuine
product projections. -/
theorem fieldGodementSkyscraperPairing_projection
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementFamilyProjectedPairing.{u, w} k M N =
      fieldGodementTensorProjectionMap.{u, w} k M N ≫ fieldGodementPointPairing.{u, w} k M N :=
  Adjunction.hom_eq_comp_of_counit_square
    ((fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))
    (fieldGodementFamilyProjectedPairing.{u, w} k M N)
    (fieldGodementTensorProjectionMap.{u, w} k M N) (fieldGodementPointPairing.{u, w} k M N)
    (fieldGodementSourceStalkTensorMap.{u, w} k M N)
    (fieldGodementTargetStalkTensorMap.{u, w} k M N)
    (fieldGodementProjectedStalkTensorMap.{u, w} k M N)
    (fieldGodementPointCounitTensor.{u, w} k M N)
    (fieldGodementFamilyCounitTensor.{u, w} k M N)
    (fieldGodementProjectedPairing_characteristic.{u, w} k M N)
    (fieldGodementPointPairing_characteristic.{u, w} k M N)
    (fieldGodementStoredProjectionTensor_naturality.{u, w} k M N)
    (fieldGodementStoredCounitTensor_comp.{u, w} k M N)

end AlgebraicGeometry.Scheme.DerivedSections
