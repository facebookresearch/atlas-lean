/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.CanonicalPrescribedPointTensorPairing

/-! # Binary pairing preservation by the actual canonical/prescribed monad iso -/

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
/-- The actual canonical-to-prescribed point monad comparison preserves its genuine binary tensor
pairing. -/
theorem fieldCanonicalPrescribedPointMonadIso_tensorPairing
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let e := fieldCanonicalPrescribedPointEndofunctorIso.{u, w} k Ω
    fieldCanonicalPointTensorPairing.{u, w} k F G ≫
        e.hom.app (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) =
      smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) (e.hom.app F) (e.hom.app G) ≫
        fieldPrescribedPointTensorPairing.{u, w} k Ω F G := by
  intro e
  let X := Spec (.of k)
  let p := fieldGodementCanonicalPoint.{u, w} k
  let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
  let L' := q.sheafFiber (A := AddCommGrpCat.{max u w})
  let A := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let B := q.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let s := fieldCanonicalSkyscraperIso.{u, w} k Ω default
  let d := (fieldCanonicalCommonStalkIso.{u, w} k Ω default).inv
  let T := smallEtaleTensorSheaf.{u, w} X F G
  let a := (smallEtalePointTensorSheafStalkIso.{u, w} X p F G).inv
  let b := (smallEtalePointTensorSheafStalkIso.{u, w} X q F G).inv
  let t := AddCommGrpCat.ofHom (TensorProduct.map
    (d.app F).hom.toIntLinearMap (d.app G).hom.toIntLinearMap).toAddMonoidHom
  let c := fieldCanonicalPointSkyscraperTensorPairing.{u, w} k (L.obj F) (L.obj G)
  let c' := fieldPointSkyscraperTensorPairing.{u, w} k Ω (L'.obj F) (L'.obj G)
  let c₀ := fieldPointSkyscraperTensorPairing.{u, w} k Ω (L.obj F) (L.obj G)
  let f := smallEtaleTensorSheafMap.{u, w} X (s.hom.app (L.obj F)) (s.hom.app (L.obj G))
  let g := smallEtaleTensorSheafMap.{u, w} X (B.map (d.app F)) (B.map (d.app G))
  have hp : c ≫ s.hom.app (AddCommGrpCat.of (L.obj F ⊗[ℤ] L.obj G)) = f ≫ c₀ :=
    fieldCanonicalSkyscraperIso_tensorPairing.{u, w} k Ω (L.obj F) (L.obj G)
  have hc : c₀ ≫ B.map t = g ≫ c' :=
    (fieldPointSkyscraperTensorPairing_naturality.{u, w} k Ω (d.app F) (d.app G)).symm
  have ht : a ≫ d.app T = t ≫ b := fieldCanonicalCommonStalkIso_tensor_inv_comm.{u, w} k Ω F G
  have he (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
      e.hom.app Q = s.hom.app (L.obj Q) ≫ B.map (d.app Q) := s.hom.naturality (d.app Q)
  have hf : smallEtaleTensorSheafMap.{u, w} X (e.hom.app F) (e.hom.app G) = f ≫ g :=
    (congrArg₂ (smallEtaleTensorSheafMap.{u, w} X) (he F) (he G)).trans
      (smallEtaleTensorSheafMap_comp.{u, w} X
        (s.hom.app (L.obj F)) (B.map (d.app F))
        (s.hom.app (L.obj G)) (B.map (d.app G))).symm
  have h := Adjunction.pairing_comparison_comp A B s.hom c c₀ c' a (d.app T) t b f g hp hc ht
  exact (congrArg (fun z => fieldCanonicalPointTensorPairing.{u, w} k F G ≫ z) (he T)).trans
    (h.trans (congrArg (fun z => z ≫ fieldPrescribedPointTensorPairing.{u, w} k Ω F G) hf.symm))

end AlgebraicGeometry.Scheme.DerivedSections
