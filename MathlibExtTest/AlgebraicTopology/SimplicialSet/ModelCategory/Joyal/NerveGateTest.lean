/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.NerveGate

/-!
# The nerve gate: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.NerveGate`:
nerve prisms and nerve chain functors with their faces, the composition
structure, identity edge, inverse data, equivalence edge and `h Fun`
isomorphism classified by nerve homotopies of natural transformations,
the backward nerve gate in `HasHoInverse`, bundled-equivalence,
`Functor.IsEquivalence` and `nerveFunctor.map` forms (including the
Stevenson Definition 2.1 equivalence-edge reading through
`SSet.HasHoInverse.exists_isEquivalence_edges`), and the forward nerve
gate with its iff forms, at an arbitrary universe and at universe `0`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial CategoryTheory.Prod

universe u v

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace NerveGateTest

section NervePrisms

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G H : C ⥤ D}

example (Φ : C × Fin 2 ⥤ D) :
    CategoryTheory.nerve C ⊗ Δ[1] ⟶ CategoryTheory.nerve D :=
  Φ.nervePrismMap

example (Φ : C × Fin 2 ⥤ D) {Δ : SimplexCategoryᵒᵖ}
    (X : (CategoryTheory.nerve C ⊗ Δ[1]).obj Δ) :
    Φ.nervePrismMap.app Δ X =
      (Φ.mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) :=
  CategoryTheory.Functor.nervePrismMap_app Φ X

example (Φ : C × Fin 3 ⥤ D) (i : Fin 3) :
    (CategoryTheory.nerve C ◁ SSet.stdSimplex.δ i) ≫ Φ.nervePrismMap =
      (((𝟭 C).prod (SimplexCategory.δ i).toOrderHom.toFunctor) ⋙
        Φ).nervePrismMap :=
  CategoryTheory.Functor.whiskerLeft_δ_nervePrismMap Φ i

example (α : F ⟶ G) :
    (CategoryTheory.NatTrans.nerveCylinderFunctor α).nervePrismMap =
      CategoryTheory.NatTrans.nerveHomotopyMap α :=
  CategoryTheory.NatTrans.nervePrismMap_nerveCylinderFunctor α

example (α : F ⟶ G) (β : G ⟶ H) : C × Fin 3 ⥤ D :=
  CategoryTheory.NatTrans.nerveChainFunctor α β

example (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFunctor) ⋙
        CategoryTheory.NatTrans.nerveChainFunctor α β =
      CategoryTheory.NatTrans.nerveCylinderFunctor α :=
  CategoryTheory.NatTrans.prod_δ_two_comp_nerveChainFunctor α β

example (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFunctor) ⋙
        CategoryTheory.NatTrans.nerveChainFunctor α β =
      CategoryTheory.NatTrans.nerveCylinderFunctor β :=
  CategoryTheory.NatTrans.prod_δ_zero_comp_nerveChainFunctor α β

example (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFunctor) ⋙
        CategoryTheory.NatTrans.nerveChainFunctor α β =
      CategoryTheory.NatTrans.nerveCylinderFunctor (α ≫ β) :=
  CategoryTheory.NatTrans.prod_δ_one_comp_nerveChainFunctor α β

example :
    CategoryTheory.NatTrans.nerveCylinderFunctor (𝟙 F) =
      CategoryTheory.Prod.fst C (Fin 2) ⋙ F :=
  CategoryTheory.NatTrans.nerveCylinderFunctor_id

example :
    (CategoryTheory.Prod.fst C (Fin 2) ⋙ F).nervePrismMap =
      SemiCartesianMonoidalCategory.fst (CategoryTheory.nerve C)
          (Δ[1] : SSet.{max u v}) ≫ CategoryTheory.nerveMap F :=
  CategoryTheory.Functor.nervePrismMap_fst_comp

end NervePrisms

section NerveHomotopyEdges

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F G H : C ⥤ D}

example (α : F ⟶ G) :
    (CategoryTheory.NatTrans.nerveHomotopy α).edgeIhom.edge =
      SSet.ihomSimplexOfPrism
        (CategoryTheory.NatTrans.nerveHomotopyMap α) :=
  SSet.nerveHomotopy_edgeIhom_edge α

example (α : F ⟶ G) (β : G ⟶ H) :
    SSet.Edge.CompStruct
      (CategoryTheory.NatTrans.nerveHomotopy α).edgeIhom
      (CategoryTheory.NatTrans.nerveHomotopy β).edgeIhom
      (CategoryTheory.NatTrans.nerveHomotopy (α ≫ β)).edgeIhom :=
  SSet.nerveHomotopy_edgeIhom_compStruct α β

example (F : C ⥤ D) :
    (CategoryTheory.NatTrans.nerveHomotopy (𝟙 F)).edgeIhom =
      SSet.Edge.id (SSet.ihomVertexEquiv (CategoryTheory.nerve C)
        (CategoryTheory.nerve D) (CategoryTheory.nerveMap F)) :=
  SSet.nerveHomotopy_id_edgeIhom F

example (α : F ≅ G) :
    (CategoryTheory.NatTrans.nerveHomotopy α.hom).edgeIhom.InvStruct :=
  SSet.nerveHomotopy_edgeIhom_invStruct α

example (α : F ≅ G) :
    (CategoryTheory.NatTrans.nerveHomotopy α.hom
      ).edgeIhom.IsEquivalence :=
  SSet.nerveHomotopy_edgeIhom_isEquivalence α

example (α : F ≅ G) :
    (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv
        (CategoryTheory.nerve C) (CategoryTheory.nerve D)
        (CategoryTheory.nerveMap F)) :
        SSet.hoFunctor.obj ((ihom (CategoryTheory.nerve C)).obj
          (CategoryTheory.nerve D))) ≅
      SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv
        (CategoryTheory.nerve C) (CategoryTheory.nerve D)
        (CategoryTheory.nerveMap G)) :=
  SSet.nerveMap_hoFunctorIso_of_natIso α

example (F : C ⥤ D) :
    (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv
        (CategoryTheory.nerve C) (CategoryTheory.nerve D)
        (CategoryTheory.nerveMap F)) :
        SSet.hoFunctor.obj ((ihom (CategoryTheory.nerve C)).obj
          (CategoryTheory.nerve D))) ≅
      SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv
        (CategoryTheory.nerve C) (CategoryTheory.nerve D)
        (CategoryTheory.nerveMap F)) :=
  SSet.nerveMap_hoFunctorIso_of_natIso (Iso.refl F)

end NerveHomotopyEdges

section BackwardGate

variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}

example (e : C ≌ D) : SSet.HasHoInverse (CategoryTheory.nerveMap e.functor) :=
  SSet.hasHoInverse_nerveMap_of_equivalence e

example (e : C ≌ D) :
    ∃ g : CategoryTheory.nerve D ⟶ CategoryTheory.nerve C,
      (∃ eX : SSet.Edge
          (SSet.ihomVertexEquiv _ _ (CategoryTheory.nerveMap e.functor ≫ g))
          (SSet.ihomVertexEquiv _ _ (𝟙 (CategoryTheory.nerve C))),
        eX.IsEquivalence) ∧
      (∃ eY : SSet.Edge
          (SSet.ihomVertexEquiv _ _ (g ≫ CategoryTheory.nerveMap e.functor))
          (SSet.ihomVertexEquiv _ _ (𝟙 (CategoryTheory.nerve D))),
        eY.IsEquivalence) :=
  (SSet.hasHoInverse_nerveMap_of_equivalence e).exists_isEquivalence_edges

example (e : C ≌ D) :
    SSet.categoricalEquivalences (CategoryTheory.nerveMap e.functor) :=
  SSet.categoricalEquivalences.nerveMap_of_equivalence e

example [F.IsEquivalence] :
    SSet.categoricalEquivalences (CategoryTheory.nerveMap F) :=
  SSet.categoricalEquivalences.nerveMap_of_isEquivalence F

example : SSet.categoricalEquivalences (CategoryTheory.nerveMap (𝟭 C)) :=
  SSet.categoricalEquivalences.nerveMap_of_isEquivalence (𝟭 C)

example {φ : Cat.of C ⟶ Cat.of D} [φ.toFunctor.IsEquivalence] :
    SSet.categoricalEquivalences (CategoryTheory.nerveFunctor.map φ) :=
  SSet.categoricalEquivalences.nerveFunctor_map_of_isEquivalence

example (e : C ≌ D) :
    SSet.categoricalEquivalences
      (CategoryTheory.nerveFunctor.map e.functor.toCatHom) := by
  have : e.functor.toCatHom.toFunctor.IsEquivalence :=
    inferInstanceAs (e.functor.IsEquivalence)
  exact SSet.categoricalEquivalences.nerveFunctor_map_of_isEquivalence

end BackwardGate

section ForwardGateAndIff

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

example (hf : SSet.categoricalEquivalences (CategoryTheory.nerveMap F)) :
    F.IsEquivalence :=
  hf.isEquivalence_of_nerveMap

example :
    SSet.categoricalEquivalences (CategoryTheory.nerveMap F) ↔
      F.IsEquivalence :=
  SSet.categoricalEquivalences_nerveMap_iff F

example (φ : Cat.of C ⟶ Cat.of D) :
    SSet.categoricalEquivalences (CategoryTheory.nerveFunctor.map φ) ↔
      φ.toFunctor.IsEquivalence :=
  SSet.categoricalEquivalences_nerveFunctor_map_iff φ

example (hf : SSet.categoricalEquivalences
    (CategoryTheory.nerveFunctor.map F.toCatHom)) : F.IsEquivalence :=
  (SSet.categoricalEquivalences_nerveFunctor_map_iff F.toCatHom).mp hf

example : (𝟭 C).IsEquivalence :=
  (SSet.categoricalEquivalences_nerveMap_iff (𝟭 C)).mp
    (SSet.categoricalEquivalences.nerveMap_of_isEquivalence (𝟭 C))

end ForwardGateAndIff

section UniverseZero

example :
    SSet.categoricalEquivalences.{0}
      (CategoryTheory.nerveMap (𝟭 (Fin 2))) :=
  SSet.categoricalEquivalences.nerveMap_of_isEquivalence (𝟭 (Fin 2))

example :
    SSet.categoricalEquivalences.{0} (CategoryTheory.nerveMap
      (CategoryTheory.Equivalence.refl (C := Fin 2)).functor) :=
  SSet.categoricalEquivalences.nerveMap_of_equivalence
    (CategoryTheory.Equivalence.refl (C := Fin 2))

example :
    SSet.categoricalEquivalences.{0}
        (CategoryTheory.nerveMap (𝟭 (Fin 2))) ↔ (𝟭 (Fin 2)).IsEquivalence :=
  SSet.categoricalEquivalences_nerveMap_iff (𝟭 (Fin 2))

example (m : (Δ[0] : SSet.{0}) ⟶ CategoryTheory.nerve (Fin 2)) :
    (SSet.hoFunNerveComparison (Δ[0] : SSet.{0}) (Fin 2)).obj
        (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv _ _ m)) =
      SSet.descNerve m :=
  SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv m

end UniverseZero

end NerveGateTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
