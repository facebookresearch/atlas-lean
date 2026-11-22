/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ScalarCircleHomGroup

/-!
# The scalar circle group functor on the whole ordinary Ho

The earned scalar circle groups and original target postcomposition maps
form a group-valued functor. An original weak map becomes an isomorphism
because the same postcomposition function is bijective in ordinary Ho.
The localization universal property supplies the complete functor on all
Ho objects and morphisms. Its underlying set functor is naturally the
original circle coyoneda functor, with the same actual map functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.ScalarCircleHoFunctor

private abbrev P := Under (Δ[0] : SSet.{v})
private abbrev H := toHomotopyCategory P.{v}
private abbrev circle := SSet.pointedCircle.{v}

/-- The actual original scalar circle group and every original pointed map form a full group functor. -/
def raw : P ⥤ GrpCat.{v + 1} where
  obj K := by
    letI := ScalarCircleHomGroup.group.{u, v} K
    exact GrpCat.of ((H).obj circle ⟶ (H).obj K)
  map {K L} k := by
    letI := ScalarCircleHomGroup.group.{u, v} K
    letI := ScalarCircleHomGroup.group.{u, v} L
    exact GrpCat.ofHom (ScalarCircleHomGroup.postcompose.{u, v} k)
  map_id K := by
    apply GrpCat.ext
    intro a
    change a ≫ (H).map (𝟙 K) = a
    rw [(H).map_id, Category.comp_id]
  map_comp k l := by
    apply GrpCat.ext
    intro a
    change a ≫ (H).map (k ≫ l) = (a ≫ (H).map k) ≫ (H).map l
    rw [(H).map_comp, Category.assoc]

/-- The underlying raw group functor retains the full original localized target postcomposition. -/
def rawUnderlyingIso : (H) ⋙ coyoneda.obj (Opposite.op ((H).obj circle)) ≅
    raw.{u, v} ⋙ forget GrpCat :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {K L} k => by
    ext a
    change a ≫ (H).map k = ScalarCircleHomGroup.postcompose.{u, v} k a
    exact (ScalarCircleHomGroup.postcompose_apply.{u, v} k a).symm)

/-- The same original weak arrow gives a bijective underlying circle map, hence a group isomorphism. -/
theorem raw_inverts : (weakEquivalences P).IsInvertedBy raw.{u, v} := by
  intro K L k hk
  let : IsIso ((H).map k) := Localization.inverts (H) (weakEquivalences P) k hk
  let : IsIso ((forget GrpCat).map ((raw.{u, v}).map k)) := by
    apply (isIso_iff_bijective _).mpr
    change Function.Bijective (fun a : (H).obj circle ⟶ (H).obj K => a ≫ (H).map k)
    let e : ((H).obj circle ⟶ (H).obj K) ≃ ((H).obj circle ⟶ (H).obj L) :=
      Iso.homCongr (Iso.refl ((H).obj circle)) (asIso ((H).map k))
    simpa only [e, Iso.homCongr, Equiv.coe_fn_mk, Iso.refl_inv, asIso_hom, Category.id_comp] using e.bijective
  exact isIso_of_reflects_iso ((raw.{u, v}).map k) (forget GrpCat)

/-- The actual scalar group functor on every original ordinary-Ho object and morphism. -/
def onHo : HomotopyCategory P ⥤ GrpCat.{v + 1} :=
  Localization.Construction.lift raw.{u, v} raw_inverts

/-- The complete original projection retains that same group functor, without changing any original map. -/
theorem projection : (H) ⋙ onHo.{u, v} = raw.{u, v} :=
  Localization.Construction.fac raw.{u, v} raw_inverts

/-- The actual localized group functor has the original circle Hom sets as its underlying set functor. -/
def underlyingIso : coyoneda.obj (Opposite.op ((H).obj circle)) ≅
    onHo.{u, v} ⋙ forget GrpCat := by
  letI : Localization.Lifting (H) (weakEquivalences P) raw.{u, v} onHo.{u, v} :=
    ⟨eqToIso projection⟩
  exact Localization.liftNatIso (H) (weakEquivalences P)
    ((H) ⋙ coyoneda.obj (Opposite.op ((H).obj circle))) (raw.{u, v} ⋙ forget GrpCat)
    (coyoneda.obj (Opposite.op ((H).obj circle))) (onHo.{u, v} ⋙ forget GrpCat)
    rawUnderlyingIso.{u, v}

/-- Both full original functions of the natural underlying isomorphism are retained on every Ho target. -/
def homEquiv (X : HomotopyCategory P) : ((H).obj circle ⟶ X) ≃ (onHo.{u, v}).obj X :=
  ((underlyingIso.{u, v}).app X).toEquiv

/-- The group on the actual full circle Hom set is earned from the localized group functor. -/
@[instance_reducible]
def group (X : HomotopyCategory P) : Group ((H).obj circle ⟶ X) :=
  EquivTransport.group (homEquiv.{u, v} X)

/-- Every original Ho target arrow gives the full circle-Hom group map. -/
def postcompose {X Y : HomotopyCategory P} (f : X ⟶ Y) :
    letI := group.{u, v} X
    letI := group.{u, v} Y
    ((H).obj circle ⟶ X) →* ((H).obj circle ⟶ Y) := by
  letI := group.{u, v} X
  letI := group.{u, v} Y
  exact EquivTransport.map (homEquiv.{u, v} X) (homEquiv.{u, v} Y)
    (fun a => a ≫ f) ((onHo.{u, v}).map f).hom
    (fun a => (underlyingIso.{u, v}).hom.naturality_apply f a)

/-- The entire localized group-map function is the same original target postcomposition. -/
theorem postcompose_apply {X Y : HomotopyCategory P} (f : X ⟶ Y) (a : (H).obj circle ⟶ X) :
    postcompose.{u, v} f a = a ≫ f := rfl

end HomotopicalAlgebra.ScalarCircleHoFunctor
