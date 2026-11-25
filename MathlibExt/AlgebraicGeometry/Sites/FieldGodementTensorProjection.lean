/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementProductCollapse
public import MathlibExt.CategoryTheory.Adjunction.ComparisonMonadIso

/-!
# Actual tensor pairing under the field Godement product projection

The original family-adjunction counit characterizes its binary pairing. Its
singleton projection is the same canonical point tensor-counit pairing.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k : Type u) [Field k]

/-- The actual canonical-point skyscraper pairing is the transpose of its original tensor
counits. -/
def fieldCanonicalPointSkyscraperTensorPairing (M N : AddCommGrpCat.{max u w}) :
    let p := fieldGodementCanonicalPoint.{u, w} k
    let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    smallEtaleTensorSheaf.{u, w} (Spec (.of k)) (R.obj M) (R.obj N) ⟶
      R.obj (AddCommGrpCat.of (M ⊗[ℤ] N)) :=
  let p := fieldGodementCanonicalPoint.{u, w} k
  let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let a := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  a.homEquiv _ _
    ((smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
      AddCommGrpCat.ofHom (TensorProduct.map
        (a.counit.app M).hom.toIntLinearMap (a.counit.app N).hom.toIntLinearMap).toAddMonoidHom)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical-point pairing has its literal tensor-of-counits characteristic. -/
theorem fieldCanonicalPointSkyscraperTensorPairing_counit (M N : AddCommGrpCat.{max u w}) :
    let p := fieldGodementCanonicalPoint.{u, w} k
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    let a := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
    L.map (fieldCanonicalPointSkyscraperTensorPairing.{u, w} k M N) ≫
        a.counit.app (AddCommGrpCat.of (M ⊗[ℤ] N)) =
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (a.counit.app M).hom.toIntLinearMap
              (a.counit.app N).hom.toIntLinearMap).toAddMonoidHom := by
  intro p L R a
  let b := (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
    AddCommGrpCat.ofHom (TensorProduct.map
      (a.counit.app M).hom.toIntLinearMap (a.counit.app N).hom.toIntLinearMap).toAddMonoidHom
  exact (a.homEquiv_counit _ _ (a.homEquiv _ _ b)).symm.trans
    ((a.homEquiv _ _).symm_apply_apply b)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Godement family pairing has its original canonical point counit characteristic after
projection. -/
theorem fieldGodementSkyscraperPairing_projection_counit
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    let X := Spec (.of k)
    let p := fieldGodementCanonicalPoint.{u, w} k
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let R := smallEtaleGodementSkyscrapers.{u, w} X
    let T := smallEtaleGodementFamilyTensor.{u, w} X M N
    let π := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (T y)) default
    L.map (smallEtaleGodementSkyscraperPairing.{u, w} X M N ≫ π) ≫
        p.skyscraperSheafAdjunction.counit.app (T default) =
      (smallEtalePointTensorSheafStalkIso.{u, w} X p (R.obj M) (R.obj N)).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (((smallEtaleGodementAdjunction.{u, w} X).counit.app M) default).hom.toIntLinearMap
          (((smallEtaleGodementAdjunction.{u, w} X).counit.app N)
              default).hom.toIntLinearMap).toAddMonoidHom := by
  intro X p L R T π
  have h := congrArg (fun f => f default)
    (smallEtaleGodementSkyscraperPairing_counit.{u, w} X M N)
  have hc := fieldGodementCounit_default.{u, w} k T
  have h' :=
      (congrArg (fun f => L.map (smallEtaleGodementSkyscraperPairing.{u, w} X M N) ≫ f) hc).symm
  exact (congrArg (fun f => f ≫ p.skyscraperSheafAdjunction.counit.app (T default))
    (L.map_comp _ _)).trans
    ((Category.assoc _ _ _).trans (h'.trans h))

set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring the two actual product-projected point counits gives the same original family counit
tensor component. -/
theorem fieldGodementProjectedCounitTensor
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    let X := Spec (.of k)
    let p := fieldGodementCanonicalPoint.{u, w} k
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let adj := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
    let πM := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) default
    let πN := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (N y)) default
    let t := AddCommGrpCat.ofHom (TensorProduct.map
      (L.map πM).hom.toIntLinearMap (L.map πN).hom.toIntLinearMap).toAddMonoidHom
    let c := AddCommGrpCat.ofHom (TensorProduct.map
      (adj.counit.app (M default)).hom.toIntLinearMap
      (adj.counit.app (N default)).hom.toIntLinearMap).toAddMonoidHom
    let d := AddCommGrpCat.ofHom (TensorProduct.map
      (((smallEtaleGodementAdjunction.{u, w} X).counit.app M) default).hom.toIntLinearMap
      (((smallEtaleGodementAdjunction.{u, w} X).counit.app N)
          default).hom.toIntLinearMap).toAddMonoidHom
    t ≫ c = d := by
  intro X p L adj πM πN t c d
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a b
    change adj.counit.app (M default) (L.map πM a) ⊗ₜ[ℤ]
        adj.counit.app (N default) (L.map πN b) =
      ((smallEtaleGodementAdjunction.{u, w} X).counit.app M) default a ⊗ₜ[ℤ]
        ((smallEtaleGodementAdjunction.{u, w} X).counit.app N) default b
    exact congrArg₂ (fun a b => a ⊗ₜ[ℤ] b)
      (ConcreteCategory.congr_hom (fieldGodementCounit_default.{u, w} k M) a).symm
      (ConcreteCategory.congr_hom (fieldGodementCounit_default.{u, w} k N) b).symm
  · intro x y hx hy
    exact ((t ≫ c).hom.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (d.hom.map_add x y).symm)

end AlgebraicGeometry.Scheme.DerivedSections
