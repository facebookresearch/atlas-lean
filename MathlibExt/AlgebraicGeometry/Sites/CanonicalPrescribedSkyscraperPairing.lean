/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.CanonicalPointTensorJoin
public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementCanonicalTensorPairing
public import MathlibExt.AlgebraicGeometry.Sites.FieldPointSkyscraperTensorPairing
public import MathlibExt.CategoryTheory.Adjunction.ComparisonMonadIso

/-!
# Tensor pairing comparison for field skyscrapers

The natural isomorphism from the canonical field-point skyscraper functor to the prescribed
one preserves the binary pairing map. This compares the maps from the tensor of two
skyscrapers to the skyscraper of the integer tensor of their coefficients.
-/

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
/-- Field skyscraper comparison preserves the binary tensor pairing.

The canonical skyscraper pairing followed by the comparison at `M ⊗[ℤ] N` equals tensoring its
components at `M` and `N` followed by the prescribed pairing. -/
theorem fieldCanonicalSkyscraperIso_tensorPairing (M N : AddCommGrpCat.{max u w}) :
    let s := fieldCanonicalSkyscraperIso.{u, w} k Ω default
    fieldCanonicalPointSkyscraperTensorPairing.{u, w} k M N ≫
        s.hom.app (AddCommGrpCat.of (M ⊗[ℤ] N)) =
      smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) (s.hom.app M) (s.hom.app N) ≫
        fieldPointSkyscraperTensorPairing.{u, w} k Ω M N := by
  intro s
  let X := Spec (.of k)
  let p := fieldGodementCanonicalPoint.{u, w} k
  let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
  let A := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let L' := q.sheafFiber (A := AddCommGrpCat.{max u w})
  let B := q.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let adj := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let adj' := q.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let e := fieldCanonicalCommonStalkIso.{u, w} k Ω default
  let T := AddCommGrpCat.of (M ⊗[ℤ] N)
  let b := fieldCanonicalPointSkyscraperTensorPairing.{u, w} k M N
  let b' := fieldPointSkyscraperTensorPairing.{u, w} k Ω M N
  let f := smallEtaleTensorSheafMap.{u, w} X (s.hom.app M) (s.hom.app N)
  have hc : L'.map (s.hom.app T) ≫ adj'.counit.app T =
      e.hom.app (A.obj T) ≫ adj.counit.app T :=
    fieldCanonicalSkyscraperIso_counit.{u, w} k Ω default T
  have hcM : L'.map (s.hom.app M) ≫ adj'.counit.app M =
      e.hom.app (A.obj M) ≫ adj.counit.app M :=
    fieldCanonicalSkyscraperIso_counit.{u, w} k Ω default M
  have hcN : L'.map (s.hom.app N) ≫ adj'.counit.app N =
      e.hom.app (A.obj N) ≫ adj.counit.app N :=
    fieldCanonicalSkyscraperIso_counit.{u, w} k Ω default N
  have hn := e.hom.naturality b
  have ht := fieldCanonicalCommonStalkIso_tensor.{u, w} k Ω default (A.obj M) (A.obj N)
  have htf := smallEtalePointTensorSheafStalkIso_naturality.{u, w} X q (s.hom.app M) (s.hom.app N)
  have hb := fieldCanonicalPointSkyscraperTensorPairing_counit.{u, w} k M N
  have hb' := fieldPointSkyscraperTensorPairing_counit.{u, w} k Ω M N
  let m := (smallEtalePointTensorSheafStalkIso.{u, w} X p (A.obj M) (A.obj N)).hom
  let n := (smallEtalePointTensorSheafStalkIso.{u, w} X q (A.obj M) (A.obj N)).hom
  let v := (smallEtalePointTensorSheafStalkIso.{u, w} X q (B.obj M) (B.obj N)).hom
  let c := AddCommGrpCat.ofHom (TensorProduct.map
    (adj.counit.app M).hom.toIntLinearMap (adj.counit.app N).hom.toIntLinearMap).toAddMonoidHom
  let c' := AddCommGrpCat.ofHom (TensorProduct.map
    (adj'.counit.app M).hom.toIntLinearMap (adj'.counit.app N).hom.toIntLinearMap).toAddMonoidHom
  let u := AddCommGrpCat.ofHom (TensorProduct.map
    (e.hom.app (A.obj M)).hom.toIntLinearMap
        (e.hom.app (A.obj N)).hom.toIntLinearMap).toAddMonoidHom
  let t := AddCommGrpCat.ofHom (TensorProduct.map
    (L'.map (s.hom.app M)).hom.toIntLinearMap
        (L'.map (s.hom.app N)).hom.toIntLinearMap).toAddMonoidHom
  let d := AddCommGrpCat.ofHom (TensorProduct.map
    (L'.map (s.hom.app M) ≫ adj'.counit.app M).hom.toIntLinearMap
    (L'.map (s.hom.app N) ≫ adj'.counit.app N).hom.toIntLinearMap).toAddMonoidHom
  have htc : t ≫ c' = d :=
    Adjunction.integerTensorMap_comp_of_comp_eq _ _ _ rfl _ _ _ rfl
  have huc : u ≫ c = d :=
    Adjunction.integerTensorMap_comp_of_comp_eq _ _ _ hcM.symm _ _ _ hcN.symm
  apply (adj'.homEquiv _ _).symm.injective
  rw [adj'.homEquiv_counit, adj'.homEquiv_counit]
  have hleft : L'.map (b ≫ s.hom.app T) ≫ adj'.counit.app T = n ≫ d := by
    rw [L'.map_comp, Category.assoc, hc, ← Category.assoc, hn, Category.assoc, hb,
      ← Category.assoc, ht, Category.assoc, huc]
  have hright : L'.map (f ≫ b') ≫ adj'.counit.app T = n ≫ d := by
    rw [L'.map_comp, Category.assoc, hb', ← Category.assoc, htf, Category.assoc, htc]
  exact hleft.trans hright.symm

end AlgebraicGeometry.Scheme.DerivedSections
