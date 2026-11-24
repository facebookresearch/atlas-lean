/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-!
# Homotopy inverses of categorical equivalences

A simplicial map has a homotopy inverse when an actual inverse map gives
isomorphisms in both ordinary homotopy categories of endofunctor objects.
A categorical equivalence between quasicategories has this datum: test the
defining equivalence at the source and target, using essential surjectivity
and full faithfulness. The argument uses the defining `hFun` test before
any model structure.

This is the homotopy-category formulation of the inverse witnesses in
Stevenson Definition 2.1. The predicate is defined for arbitrary simplicial
sets; the construction below requires quasicategory source and target.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/-- A map has a homotopy inverse when an actual reverse map supplies both
inverse isomorphisms in the ordinary homotopy categories of functor objects. -/
def HasHoInverse (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X,
    Nonempty ((HomotopyCategory.mk (ihomVertexEquiv X X (f ≫ g)) :
        hoFunctor.obj ((ihom X).obj X)) ≅
      HomotopyCategory.mk (ihomVertexEquiv X X (𝟙 X))) ∧
    Nonempty ((HomotopyCategory.mk (ihomVertexEquiv Y Y (g ≫ f)) :
        hoFunctor.obj ((ihom Y).obj Y)) ≅
      HomotopyCategory.mk (ihomVertexEquiv Y Y (𝟙 Y)))

/-- A categorical equivalence between quasicategories has a simplicial
inverse with both required `hFun` isomorphisms. -/
theorem categoricalEquivalences.hasHoInverse [Quasicategory X]
    [Quasicategory Y] (hf : categoricalEquivalences f) :
    HasHoInverse f := by
  have : (hoFunctor.map ((pre f).app X)).toFunctor.IsEquivalence :=
    hf X inferInstance
  obtain ⟨a, ⟨α⟩⟩ := Functor.EssSurj.mem_essImage
    (hoFunctor.map ((pre f).app X)).toFunctor
    (HomotopyCategory.mk (ihomVertexEquiv X X (𝟙 X)))
  obtain ⟨g, rfl⟩ : ∃ m : Y ⟶ X,
      a = HomotopyCategory.mk (ihomVertexEquiv Y X m) := by
    refine ⟨(ihomVertexEquiv Y X).symm (HomotopyCategory.objEquiv a), ?_⟩
    rw [Equiv.apply_symm_apply]
    exact (HomotopyCategory.objEquiv.left_inv a).symm
  change (mapHomotopyCategory ((pre f).app X)).obj
      (HomotopyCategory.mk (ihomVertexEquiv Y X g)) ≅
    HomotopyCategory.mk (ihomVertexEquiv X X (𝟙 X)) at α
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_pre_app] at α
  refine ⟨g, ⟨α⟩, ?_⟩
  have : (hoFunctor.map ((pre f).app Y)).toFunctor.IsEquivalence :=
    hf Y inferInstance
  have hpost : (HomotopyCategory.mk (ihomVertexEquiv X Y (f ≫ g ≫ f)) :
        hoFunctor.obj ((ihom X).obj Y)) ≅
      HomotopyCategory.mk (ihomVertexEquiv X Y f) := by
    have h := (mapHomotopyCategory ((ihom X).map f)).mapIso α
    rw [mapHomotopyCategory_obj_mk, mapHomotopyCategory_obj_mk,
      ihomVertexEquiv_ihom_map, ihomVertexEquiv_ihom_map] at h
    rwa [Category.id_comp, Category.assoc] at h
  have hpre : (hoFunctor.map ((pre f).app Y)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv Y Y (g ≫ f))) ≅
      (hoFunctor.map ((pre f).app Y)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv Y Y (𝟙 Y))) := by
    change (mapHomotopyCategory ((pre f).app Y)).obj
        (HomotopyCategory.mk (ihomVertexEquiv Y Y (g ≫ f))) ≅
      (mapHomotopyCategory ((pre f).app Y)).obj
        (HomotopyCategory.mk (ihomVertexEquiv Y Y (𝟙 Y)))
    rw [mapHomotopyCategory_obj_mk, mapHomotopyCategory_obj_mk,
      ihomVertexEquiv_pre_app, ihomVertexEquiv_pre_app, Category.comp_id]
    exact hpost
  exact ⟨(hoFunctor.map ((pre f).app Y)).toFunctor.preimageIso hpre⟩

end SSet
