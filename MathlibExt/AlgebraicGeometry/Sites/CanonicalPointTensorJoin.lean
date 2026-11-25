/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.CanonicalPointClosureJoin
public import MathlibExt.AlgebraicGeometry.Sites.FieldPointTensorCoefficients

/-! # Actual canonical and prescribed field point tensor squares -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine prescribed-to-canonical stalk comparison preserves the same original binary
tensor. -/
theorem fieldCanonicalCommonStalkIso_tensor (x : Spec (.of k))
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let p := smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)
    let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let e := fieldCanonicalCommonStalkIso.{u, w} k Ω x
    e.hom.app (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≫
        (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p F G).hom =
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) q F G).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (e.hom.app F).hom.toIntLinearMap (e.hom.app G).hom.toIntLinearMap).toAddMonoidHom := by
  intro p q e
  exact smallEtalePointTensorSheafStalkIso_point_naturality.{u, w} (Spec (.of k))
    (fieldCanonicalCommonPointIso.{u, w} k Ω x).hom F G

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse genuine canonical-to-prescribed stalk comparison preserves the same original binary
tensor. -/
theorem fieldCanonicalCommonStalkIso_inv_tensor (x : Spec (.of k))
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let p := smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)
    let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let e := fieldCanonicalCommonStalkIso.{u, w} k Ω x
    e.inv.app (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≫
        (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) q F G).hom =
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p F G).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (e.inv.app F).hom.toIntLinearMap (e.inv.app G).hom.toIntLinearMap).toAddMonoidHom := by
  intro p q e
  exact smallEtalePointTensorSheafStalkIso_point_naturality.{u, w} (Spec (.of k))
    (fieldCanonicalCommonPointIso.{u, w} k Ω x).inv F G

end AlgebraicGeometry.Scheme.DerivedSections
