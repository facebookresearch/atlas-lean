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

/-!
# Godement and point pairings over a field

Let k be a field in universe u, X = Spec k and c = max(u, w).
For families M, N of abelian coefficient groups over X, the Godement
right adjoint R_G is the product of their point skyscrapers.
Write π_M and π_N for projection to the canonical geometric point p
over X's unique point, and π_(M⊗N) for the corresponding target projection.

The Godement tensor pairing agrees with the point tensor pairing after
these projections:
π_(M⊗N) ∘ μ_G = μ_p ∘ (π_M ⊗_sheaf π_N).
The equality concerns the sheafified tensor product over ℤ and follows
from their point-adjunction counit formulas.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a field in universe u, X = Spec k and c = max(u, w),
and let M_y, N_y be families of abelian groups in universe c over X.
Let μ_G be the product-skyscraper Godement tensor pairing and μ_p the
canonical point skyscraper pairing at the unique point *.
With product projections π_M, π_N and π_(M⊗N), the square commutes:
π_(M⊗N) ∘ μ_G = μ_p ∘ (π_M ⊗_sheaf π_N).
The tensor sheaves and coefficient tensors are over ℤ. -/
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
