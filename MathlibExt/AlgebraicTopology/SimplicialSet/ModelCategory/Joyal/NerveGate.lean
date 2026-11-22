/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CoherentIsoEndpoint
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso
public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Equivalences of categories and categorical nerve maps

The nerve of an ordinary functor is a categorical equivalence precisely
when the functor is an equivalence, in the stated object and hom universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial CategoryTheory.Prod

universe u

namespace SSet

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F G H : C ⥤ D}

/-!
## Edges of functor objects from nerve homotopies
-/

/-- The `1`-simplex underlying the edge of `Fun(nerve C, nerve D)`
classified by the nerve homotopy of `α` is the prism simplex of its
nerve homotopy map. -/
lemma nerveHomotopy_edgeIhom_edge (α : F ⟶ G) :
    (CategoryTheory.NatTrans.nerveHomotopy α).edgeIhom.edge =
      ihomSimplexOfPrism (CategoryTheory.NatTrans.nerveHomotopyMap α) :=
  rfl

/-- **Composition of nerve homotopy edges.** The `Δ[2]`-prism of the
nerve chain functor of `α` and `β` is a composition structure in
`Fun(nerve C, nerve D)` witnessing that the edge classified by
`α ≫ β` is the composite of the edges classified by `α` and `β`; its
three faces are computed by
`CategoryTheory.Functor.whiskerLeft_δ_nervePrismMap` and the nerve
chain face lemmas. -/
noncomputable def nerveHomotopy_edgeIhom_compStruct (α : F ⟶ G)
    (β : G ⟶ H) :
    Edge.CompStruct (CategoryTheory.NatTrans.nerveHomotopy α).edgeIhom
      (CategoryTheory.NatTrans.nerveHomotopy β).edgeIhom
      (CategoryTheory.NatTrans.nerveHomotopy (α ≫ β)).edgeIhom := by
  refine Edge.CompStruct.mk
    (ihomSimplexOfPrism
      (CategoryTheory.NatTrans.nerveChainFunctor α β).nervePrismMap)
    ?_ ?_ ?_
  · rw [δ_ihomSimplexOfPrism,
      CategoryTheory.Functor.whiskerLeft_δ_nervePrismMap,
      CategoryTheory.NatTrans.prod_δ_two_comp_nerveChainFunctor,
      CategoryTheory.NatTrans.nervePrismMap_nerveCylinderFunctor]
    rfl
  · rw [δ_ihomSimplexOfPrism,
      CategoryTheory.Functor.whiskerLeft_δ_nervePrismMap,
      CategoryTheory.NatTrans.prod_δ_zero_comp_nerveChainFunctor,
      CategoryTheory.NatTrans.nervePrismMap_nerveCylinderFunctor]
    rfl
  · rw [δ_ihomSimplexOfPrism,
      CategoryTheory.Functor.whiskerLeft_δ_nervePrismMap,
      CategoryTheory.NatTrans.prod_δ_one_comp_nerveChainFunctor,
      CategoryTheory.NatTrans.nervePrismMap_nerveCylinderFunctor]
    rfl

/-- The edge of `Fun(nerve C, nerve D)` classified by the nerve
homotopy of the identity natural transformation of `F` is the
identity edge at the vertex classified by `nerveMap F`: the nerve
homotopy is the constant homotopy, by
`CategoryTheory.NatTrans.nerveCylinderFunctor_id` and
`CategoryTheory.Functor.nervePrismMap_fst_comp`. -/
theorem nerveHomotopy_id_edgeIhom (F : C ⥤ D) :
    (CategoryTheory.NatTrans.nerveHomotopy (𝟙 F)).edgeIhom =
      Edge.id (ihomVertexEquiv (CategoryTheory.nerve C)
        (CategoryTheory.nerve D) (CategoryTheory.nerveMap F)) := by
  have h : (CategoryTheory.NatTrans.nerveHomotopy (𝟙 F)).h =
      (Homotopy.reflH (CategoryTheory.nerveMap F)).h := by
    rw [Homotopy.reflH_h]
    change CategoryTheory.NatTrans.nerveHomotopyMap (𝟙 F) = _
    rw [← CategoryTheory.NatTrans.nervePrismMap_nerveCylinderFunctor,
      CategoryTheory.NatTrans.nerveCylinderFunctor_id,
      CategoryTheory.Functor.nervePrismMap_fst_comp]
  rw [← Homotopy.edgeIhom_reflH]
  apply Edge.ext
  rw [Homotopy.edgeIhom_edge, Homotopy.edgeIhom_edge, h]

/-- **Inverse data for nerve homotopy edges of natural
isomorphisms.** The edge of `Fun(nerve C, nerve D)` classified by the
nerve homotopy of `α.hom` has inverse the edge classified by
`α.inv`, with composition structures from
`SSet.nerveHomotopy_edgeIhom_compStruct` at the two inverse
composites, transported along `SSet.nerveHomotopy_id_edgeIhom`. -/
noncomputable def nerveHomotopy_edgeIhom_invStruct (α : F ≅ G) :
    (CategoryTheory.NatTrans.nerveHomotopy α.hom).edgeIhom.InvStruct where
  inv := (CategoryTheory.NatTrans.nerveHomotopy α.inv).edgeIhom
  homInvId := (nerveHomotopy_edgeIhom_compStruct α.hom α.inv).ofEq
    rfl rfl (by
      rw [Iso.hom_inv_id]
      exact congrArg Edge.edge (nerveHomotopy_id_edgeIhom F))
  invHomId := (nerveHomotopy_edgeIhom_compStruct α.inv α.hom).ofEq
    rfl rfl (by
      rw [Iso.inv_hom_id]
      exact congrArg Edge.edge (nerveHomotopy_id_edgeIhom G))

/-- The edge of the functor quasicategory `Fun(nerve C, nerve D)`
classified by the nerve homotopy of a natural isomorphism is an
equivalence edge. -/
theorem nerveHomotopy_edgeIhom_isEquivalence (α : F ≅ G) :
    (CategoryTheory.NatTrans.nerveHomotopy α.hom).edgeIhom.IsEquivalence :=
  (nerveHomotopy_edgeIhom_invStruct α).isEquivalence

/-- A natural isomorphism `α : F ≅ G` determines an isomorphism in
`h Fun(nerve C, nerve D)` between the vertices classified by
`nerveMap F` and `nerveMap G`, through `SSet.Edge.InvStruct.toHoIso`
applied to the nerve homotopy edge of `α`. -/
noncomputable def nerveMap_hoFunctorIso_of_natIso (α : F ≅ G) :
    (HomotopyCategory.mk (ihomVertexEquiv (CategoryTheory.nerve C)
        (CategoryTheory.nerve D) (CategoryTheory.nerveMap F)) :
        hoFunctor.obj ((ihom (CategoryTheory.nerve C)).obj
          (CategoryTheory.nerve D))) ≅
      HomotopyCategory.mk (ihomVertexEquiv (CategoryTheory.nerve C)
        (CategoryTheory.nerve D) (CategoryTheory.nerveMap G)) :=
  (nerveHomotopy_edgeIhom_invStruct α).toHoIso

/-!
## The backward nerve gate
-/

/-- **The nerve of an equivalence is an equivalence in the sense of
Stevenson Definition 2.1 (`h Fun`-form).** For `e : C ≌ D`, the
quasi-inverse is `nerveMap e.inverse`, and the isomorphisms in
`h Fun(nerve C, nerve C)` and `h Fun(nerve D, nerve D)` are
`SSet.nerveMap_hoFunctorIso_of_natIso` of the unit and counit,
transported along `CategoryTheory.nerveMap_comp` and
`CategoryTheory.nerveMap_id`. -/
theorem hasHoInverse_nerveMap_of_equivalence (e : C ≌ D) :
    HasHoInverse (CategoryTheory.nerveMap e.functor) := by
  refine ⟨CategoryTheory.nerveMap e.inverse, ⟨?_⟩, ⟨?_⟩⟩
  · exact (eqToIso (congrArg
        (fun m => HomotopyCategory.mk
          (ihomVertexEquiv (CategoryTheory.nerve C)
            (CategoryTheory.nerve C) m))
        (CategoryTheory.nerveMap_comp e.functor e.inverse))) ≪≫
      nerveMap_hoFunctorIso_of_natIso e.unitIso.symm ≪≫
      (eqToIso (congrArg
        (fun m => HomotopyCategory.mk
          (ihomVertexEquiv (CategoryTheory.nerve C)
            (CategoryTheory.nerve C) m))
        CategoryTheory.nerveMap_id))
  · exact (eqToIso (congrArg
        (fun m => HomotopyCategory.mk
          (ihomVertexEquiv (CategoryTheory.nerve D)
            (CategoryTheory.nerve D) m))
        (CategoryTheory.nerveMap_comp e.inverse e.functor))) ≪≫
      nerveMap_hoFunctorIso_of_natIso e.counitIso ≪≫
      (eqToIso (congrArg
        (fun m => HomotopyCategory.mk
          (ihomVertexEquiv (CategoryTheory.nerve D)
            (CategoryTheory.nerve D) m))
        CategoryTheory.nerveMap_id))

/-- **Backward nerve gate for bundled equivalences:** the nerve of
the forward functor of `e : C ≌ D` is a Joyal categorical
equivalence, by the supporting results through `SSet.HasHoInverse`. -/
theorem categoricalEquivalences.nerveMap_of_equivalence (e : C ≌ D) :
    categoricalEquivalences (CategoryTheory.nerveMap e.functor) :=
  (hasHoInverse_nerveMap_of_equivalence e).categoricalEquivalences

/-- **Backward nerve gate:** if `F : C ⥤ D` is an equivalence of
ordinary categories then `CategoryTheory.nerveMap F` is a Joyal
categorical equivalence. This discharges
the additional comparison obligation/the additional comparison obligation and subsumes the
strict gate `SSet.categoricalEquivalences.nerveMap_of_isIso_toCatHom`. -/
theorem categoricalEquivalences.nerveMap_of_isEquivalence (F : C ⥤ D)
    [F.IsEquivalence] :
    categoricalEquivalences (CategoryTheory.nerveMap F) := by
  rw [← CategoryTheory.Functor.asEquivalence_functor F]
  exact categoricalEquivalences.nerveMap_of_equivalence F.asEquivalence

/-- Backward nerve gate, `CategoryTheory.nerveFunctor.map` form: if
`φ.toFunctor` is an equivalence of categories then
`CategoryTheory.nerveFunctor.map φ` is a Joyal categorical
equivalence (`nerveFunctor.map φ` is definitionally
`nerveMap φ.toFunctor`). -/
theorem categoricalEquivalences.nerveFunctor_map_of_isEquivalence
    {φ : Cat.of C ⟶ Cat.of D} [φ.toFunctor.IsEquivalence] :
    categoricalEquivalences (CategoryTheory.nerveFunctor.map φ) :=
  categoricalEquivalences.nerveMap_of_isEquivalence φ.toFunctor

/-!
## The forward nerve gate and the iff
-/

variable {X Y : Cat.{u, u}} (e : X ≅ Y)

/-- The forward functor of an isomorphism in `Cat` is an equivalence
of categories, with quasi-inverse the backward functor and strict
unit and counit. -/
private theorem isEquivalence_catIso_hom_toFunctor :
    e.hom.toFunctor.IsEquivalence := by
  have h1 : e.hom.toFunctor ⋙ e.inv.toFunctor = 𝟭 ↥X :=
    congrArg Cat.Hom.toFunctor e.hom_inv_id
  have h2 : e.inv.toFunctor ⋙ e.hom.toFunctor = 𝟭 ↥Y :=
    congrArg Cat.Hom.toFunctor e.inv_hom_id
  exact Functor.IsEquivalence.mk' e.inv.toFunctor (eqToIso h1.symm)
    (eqToIso h2)

/-- The backward functor of an isomorphism in `Cat` is an equivalence
of categories. -/
private theorem isEquivalence_catIso_inv_toFunctor :
    e.inv.toFunctor.IsEquivalence :=
  isEquivalence_catIso_hom_toFunctor e.symm

variable {F : C ⥤ D}

/-- **Forward nerve gate:** if `CategoryTheory.nerveMap F` is a
categorical equivalence then `F` is an equivalence of ordinary
categories. By the supporting results,
`(SSet.hoFunctor.map (nerveFunctor.map F.toCatHom)).toFunctor` is an
equivalence (`SSet.categoricalEquivalences.isEquivalence_hoFunctor_map`),
and naturality of `CategoryTheory.nerveFunctorCompHoFunctorIso` at
`F.toCatHom` writes `F.toCatHom` as that map conjugated by the counit
isomorphisms in `Cat`, whose underlying functors are equivalences.
This discharges the additional comparison obligation/the additional comparison obligation. -/
theorem categoricalEquivalences.isEquivalence_of_nerveMap
    (hf : categoricalEquivalences (CategoryTheory.nerveMap F)) :
    F.IsEquivalence := by
  have hnat :
      hoFunctor.map (CategoryTheory.nerveFunctor.map F.toCatHom) ≫
          (CategoryTheory.nerveFunctorCompHoFunctorIso.app
            (Cat.of D)).hom =
        (CategoryTheory.nerveFunctorCompHoFunctorIso.app
            (Cat.of C)).hom ≫ F.toCatHom :=
    CategoryTheory.nerveFunctorCompHoFunctorIso.hom.naturality
      F.toCatHom
  have hCat := congrArg
    (fun t => (CategoryTheory.nerveFunctorCompHoFunctorIso.app
      (Cat.of C)).inv ≫ t) hnat
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at hCat
  have hF : F =
      (CategoryTheory.nerveFunctorCompHoFunctorIso.app
          (Cat.of C)).inv.toFunctor ⋙
        (hoFunctor.map
          (CategoryTheory.nerveFunctor.map F.toCatHom)).toFunctor ⋙
          (CategoryTheory.nerveFunctorCompHoFunctorIso.app
            (Cat.of D)).hom.toFunctor :=
    congrArg Cat.Hom.toFunctor hCat.symm
  have hmid : (hoFunctor.map
        (CategoryTheory.nerveFunctor.map F.toCatHom)
      ).toFunctor.IsEquivalence :=
    hf.isEquivalence_hoFunctor_map
  have hleft : (CategoryTheory.nerveFunctorCompHoFunctorIso.app
        (Cat.of C)).inv.toFunctor.IsEquivalence :=
    isEquivalence_catIso_inv_toFunctor
      (CategoryTheory.nerveFunctorCompHoFunctorIso.app (Cat.of C))
  have hright : (CategoryTheory.nerveFunctorCompHoFunctorIso.app
        (Cat.of D)).hom.toFunctor.IsEquivalence :=
    isEquivalence_catIso_hom_toFunctor
      (CategoryTheory.nerveFunctorCompHoFunctorIso.app (Cat.of D))
  rw [hF]
  infer_instance

/-- **The nerve gate, iff form:** the nerve map of `F` is a Joyal
categorical equivalence if and only if `F` is an equivalence of
ordinary categories. -/
theorem categoricalEquivalences_nerveMap_iff (F : C ⥤ D) :
    categoricalEquivalences (CategoryTheory.nerveMap F) ↔
      F.IsEquivalence :=
  ⟨fun hf => hf.isEquivalence_of_nerveMap, fun h => by
    have : F.IsEquivalence := h
    exact categoricalEquivalences.nerveMap_of_isEquivalence F⟩

/-- The nerve gate in `CategoryTheory.nerveFunctor.map` form:
`nerveFunctor.map φ` is a categorical equivalence if and only if
`φ.toFunctor` is an equivalence of categories (`nerveFunctor.map φ`
is definitionally `nerveMap φ.toFunctor`). -/
theorem categoricalEquivalences_nerveFunctor_map_iff
    (φ : Cat.of C ⟶ Cat.of D) :
    categoricalEquivalences (CategoryTheory.nerveFunctor.map φ) ↔
      φ.toFunctor.IsEquivalence :=
  categoricalEquivalences_nerveMap_iff φ.toFunctor

end SSet

end
