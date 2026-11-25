/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementTensorProjectionComparison

/-! # The original Godement binary pairing under the canonical point collapse -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

/-- The genuine canonical point adjunction monad has the binary tensor-counit pairing. -/
def fieldCanonicalPointTensorPairing
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let p := fieldGodementCanonicalPoint.{u, w} k
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    smallEtaleTensorSheaf.{u, w} (Spec (.of k)) (R.obj (L.obj F)) (R.obj (L.obj G)) ⟶
      R.obj (L.obj (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)) :=
  let p := fieldGodementCanonicalPoint.{u, w} k
  let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
  let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  fieldCanonicalPointSkyscraperTensorPairing.{u, w} k (L.obj F) (L.obj G) ≫
    R.map (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p F G).inv

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Godement-to-canonical point monad collapse preserves its binary pairing. -/
theorem fieldGodementCanonicalTensorPairing_comm
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleGodementTensorPairing.{u, w} (Spec (.of k)) F G ≫
        (fieldGodementProductCollapseIso.{u, w} k).hom.app
          (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) =
      smallEtaleTensorSheafMap.{u, w} (Spec (.of k))
          ((fieldGodementProductCollapseIso.{u, w} k).hom.app F)
          ((fieldGodementProductCollapseIso.{u, w} k).hom.app G) ≫
        fieldCanonicalPointTensorPairing.{u, w} k F G := by
  let X := Spec (.of k)
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let p := fieldGodementCanonicalPoint.{u, w} k
  let M := L.obj F
  let N := L.obj G
  let T := smallEtaleGodementFamilyTensor.{u, w} X M N
  let V := L.obj (smallEtaleTensorSheaf.{u, w} X F G)
  let a := (smallEtaleGodementStalkTensorIso.{u, w} X F G).inv
  have hn := smallEtaleGodementSkyscrapers_map_projection.{u, w} X a default
  have hp := fieldGodementSkyscraperPairing_projection.{u, w} k M N
  change (smallEtaleGodementSkyscraperPairing.{u, w} X M N ≫ R.map a) ≫
      fieldGodementFamilyProjection.{u, w} k V = _
  rw [Category.assoc]
  have h := congrArg (fun f => smallEtaleGodementSkyscraperPairing.{u, w} X M N ≫ f) hn
  exact h.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ p.skyscraperSheafFunctor.map (a default)) hp).trans
      (Category.assoc _ _ _)))

end AlgebraicGeometry.Scheme.DerivedSections
