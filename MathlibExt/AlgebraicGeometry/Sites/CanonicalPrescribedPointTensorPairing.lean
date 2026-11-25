/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.CanonicalPrescribedSkyscraperPairing
public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementPrescribedPointMonad

/-! # The actual prescribed field-point monad binary pairing -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The actual prescribed Ω point monad has the binary pairing given by its original tensor
counits. -/
def fieldPrescribedPointTensorPairing
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheaf.{u, w} (Spec (.of k))
        ((fieldPrescribedPointMonad.{u, w} k Ω).obj F)
        ((fieldPrescribedPointMonad.{u, w} k Ω).obj G) ⟶
      (fieldPrescribedPointMonad.{u, w} k Ω).obj
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) :=
  let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let L := q.sheafFiber (A := AddCommGrpCat.{max u w})
  let R := q.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  fieldPointSkyscraperTensorPairing.{u, w} k Ω (L.obj F) (L.obj G) ≫
    R.map (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) q F G).inv

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual prescribed-point skyscraper pairing is natural in its original additive coefficient
maps. -/
theorem fieldPointSkyscraperTensorPairing_naturality
    {M M' N N' : AddCommGrpCat.{max u w}} (f : M ⟶ M') (g : N ⟶ N') :
    let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let R := q.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) (R.map f) (R.map g) ≫
        fieldPointSkyscraperTensorPairing.{u, w} k Ω M' N' =
      fieldPointSkyscraperTensorPairing.{u, w} k Ω M N ≫
        R.map (AddCommGrpCat.ofHom (TensorProduct.map
          f.hom.toIntLinearMap g.hom.toIntLinearMap).toAddMonoidHom) := by
  intro q R
  let X := Spec (.of k)
  let L := q.sheafFiber (A := AddCommGrpCat.{max u w})
  let adj := q.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let a := smallEtaleTensorSheafMap.{u, w} X (R.map f) (R.map g)
  let e := (smallEtalePointTensorSheafStalkIso.{u, w} X q (R.obj M) (R.obj N)).hom
  let e' := (smallEtalePointTensorSheafStalkIso.{u, w} X q (R.obj M') (R.obj N')).hom
  let t :=
      AddCommGrpCat.ofHom
      (TensorProduct.map f.hom.toIntLinearMap g.hom.toIntLinearMap).toAddMonoidHom
  let c := AddCommGrpCat.ofHom (TensorProduct.map
    (adj.counit.app M).hom.toIntLinearMap (adj.counit.app N).hom.toIntLinearMap).toAddMonoidHom
  let c' := AddCommGrpCat.ofHom (TensorProduct.map
    (adj.counit.app M').hom.toIntLinearMap (adj.counit.app N').hom.toIntLinearMap).toAddMonoidHom
  let u := AddCommGrpCat.ofHom (TensorProduct.map
    (L.map (R.map f)).hom.toIntLinearMap (L.map (R.map g)).hom.toIntLinearMap).toAddMonoidHom
  have hu : u ≫ c' = c ≫ t := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    refine TensorProduct.inductionOn x ?_ ?_
    · intro x y
      change adj.counit.app M' (L.map (R.map f) x) ⊗ₜ[ℤ]
          adj.counit.app N' (L.map (R.map g) y) =
              f (adj.counit.app M x) ⊗ₜ[ℤ] g (adj.counit.app N y)
      exact congrArg₂ (fun x y => x ⊗ₜ[ℤ] y)
        (ConcreteCategory.congr_hom (adj.counit.naturality f) x)
        (ConcreteCategory.congr_hom (adj.counit.naturality g) y)
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have hn := smallEtalePointTensorSheafStalkIso_naturality.{u, w} X q (R.map f) (R.map g)
  have hc : L.map a ≫ e' ≫ c' = (e ≫ c) ≫ t := by
    rw [← Category.assoc, hn, Category.assoc, hu, ← Category.assoc]
  change a ≫ adj.homEquiv _ _ (e' ≫ c') = adj.homEquiv _ _ (e ≫ c) ≫ R.map t
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right, hc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The real canonical-to-prescribed stalk comparison commutes with the inverse binary tensor stalk
maps. -/
theorem fieldCanonicalCommonStalkIso_tensor_inv_comm
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let p := fieldGodementCanonicalPoint.{u, w} k
    let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let e := fieldCanonicalCommonStalkIso.{u, w} k Ω default
    let t := AddCommGrpCat.ofHom (TensorProduct.map
      (e.inv.app F).hom.toIntLinearMap (e.inv.app G).hom.toIntLinearMap).toAddMonoidHom
    (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p F G).inv ≫
        e.inv.app (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) =
      t ≫ (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) q F G).inv := by
  intro p q e t
  let a := smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p F G
  let b := smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) q F G
  have h := fieldCanonicalCommonStalkIso_inv_tensor.{u, w} k Ω default F G
  apply (cancel_mono b.hom).1
  rw [Category.assoc, h, ← Category.assoc, a.inv_hom_id, Category.id_comp,
    Category.assoc, b.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.DerivedSections
