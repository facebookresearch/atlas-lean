/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.PushoutProductFunctor
public import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily
public import MathlibExt.AlgebraicTopology.ModelCategory.CartesianSM7

/-!
# Transport of free-pair pushout products

A full comparison of two input functors with a separate output left adjoint
transports both legs of the original tensor pushout. The generator reduction
retains both correlated source labels and their complete arrows.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped MonoidalCategory

namespace CategoryTheory.FreePairTransport

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

/-- The entire pair comparison read at the original named coefficient-object endpoints. -/
def componentOnObjects (F G L : C ⥤ D)
    (pair : F.prod G ⋙ tensor D ≅ tensor C ⋙ L)
    (X Y : C) {A B T : D}
    (er : F.obj X ≅ A) (es : G.obj Y ≅ B) (eo : L.obj (X ⊗ Y) ≅ T) :
    A ⊗ B ≅ T :=
  tensorIso er.symm es.symm ≪≫ pair.app (X, Y) ≪≫ eo

/-- The original entire hom survives with precisely the two input and output comparisons. -/
theorem componentOnObjects_hom (F G L : C ⥤ D)
    (pair : F.prod G ⋙ tensor D ≅ tensor C ⋙ L)
    (X Y : C) {A B T : D}
    (er : F.obj X ≅ A) (es : G.obj Y ≅ B) (eo : L.obj (X ⊗ Y) ≅ T) :
    (componentOnObjects F G L pair X Y er es eo).hom =
      (er.inv ⊗ₘ es.inv) ≫ pair.hom.app (X, Y) ≫ eo.hom := rfl

/-- The original entire inverse survives the same complete comparisons in reverse. -/
theorem componentOnObjects_inv (F G L : C ⥤ D)
    (pair : F.prod G ⋙ tensor D ≅ tensor C ⋙ L)
    (X Y : C) {A B T : D}
    (er : F.obj X ≅ A) (es : G.obj Y ≅ B) (eo : L.obj (X ⊗ Y) ≅ T) :
    (componentOnObjects F G L pair X Y er es eo).inv =
      eo.inv ≫ pair.inv.app (X, Y) ≫ (er.hom ⊗ₘ es.hom) := by
  simp only [componentOnObjects, Iso.trans_inv, tensorIso_inv, Iso.symm_inv, Iso.app_inv, Category.assoc]

/-- The curried tensor of the two original input functors. -/
abbrev pairedTensor (F G : C ⥤ D) : C ⥤ C ⥤ D :=
  F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft C D D).obj G

/-- A complete pair comparison induces the same comparison in curried form. -/
def pairedTensorIso (F G L : C ⥤ D)
    (e : F.prod G ⋙ tensor D ≅ tensor C ⋙ L) :
    pairedTensor F G ≅ curriedTensorPost L :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => e.app (X, Y)) (by
      intro Y Y' g
      change (F.obj X ◁ G.map g) ≫ e.hom.app (X, Y') =
        e.hom.app (X, Y) ≫ L.map (X ◁ g)
      have h := e.hom.naturality (show (X, Y) ⟶ (X, Y') from (𝟙 X, g))
      change (F.map (𝟙 X) ⊗ₘ G.map g) ≫ e.hom.app (X, Y') =
        e.hom.app (X, Y) ≫ L.map (𝟙 X ⊗ₘ g) at h
      rw [F.map_id, id_tensorHom, id_tensorHom] at h
      exact h))
    (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      change (F.map f ▷ G.obj Y) ≫ e.hom.app (X', Y) =
        e.hom.app (X, Y) ≫ L.map (f ▷ Y)
      have h := e.hom.naturality (show (X, Y) ⟶ (X', Y) from (f, 𝟙 Y))
      change (F.map f ⊗ₘ G.map (𝟙 Y)) ≫ e.hom.app (X', Y) =
        e.hom.app (X, Y) ≫ L.map (f ⊗ₘ 𝟙 Y) at h
      rw [G.map_id, tensorHom_id, tensorHom_id] at h
      exact h)

/-- Transport the original coefficient pushout through a proved pair
comparison and its actual output left adjoint.

The two-leg transport follows the existing `mapArrowPushoutProductIso`
implementation (historical authors @toskua, Avocado), with independent input
functors and the given full natural isomorphism replacing a monoidal functor.
-/
def pairPushoutProductIso [HasPushouts C] [HasPushouts D]
    (F G L : C ⥤ D) [L.IsLeftAdjoint]
    (e : F.prod G ⋙ tensor D ≅ tensor C ⋙ L)
    {A B K T : C} (i : A ⟶ B) (j : K ⟶ T) :
    L.mapArrow.obj (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j) ≅
      CategoryTheory.Arrow.mk (F.map i) □ CategoryTheory.Arrow.mk (G.map j) := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) i j
  let mappedSq : (curriedTensorPost L).PushoutObjObj i j :=
    { pt := L.obj sq.pt
      inl := L.map sq.inl
      inr := L.map sq.inr
      isPushout := L.map_isPushout sq.isPushout
      ι := L.map sq.ι
      inl_ι := by
        rw [← L.map_comp, sq.inl_ι]
        rfl
      inr_ι := by
        rw [← L.map_comp, sq.inr_ι]
        rfl }
  let targetSq := mappedSq.ofNatIso (pairedTensorIso F G L e).symm
  let standardSq := Functor.PushoutObjObj.ofHasPushout (pairedTensor F G) i j
  let eLeft := targetSq.isPushout.isoIsPushout _ _ standardSq.isPushout
  have hι : eLeft.hom ≫ standardSq.ι = targetSq.ι := by
    apply targetSq.isPushout.hom_ext
    · rw [targetSq.isPushout.inl_isoIsPushout_hom_assoc _ _ standardSq.isPushout]
      rw [standardSq.inl_ι]
      exact targetSq.inl_ι.symm
    · rw [targetSq.isPushout.inr_isoIsPushout_hom_assoc _ _ standardSq.isPushout]
      rw [standardSq.inr_ι]
      exact targetSq.inr_ι.symm
  change CategoryTheory.Arrow.mk (L.map sq.ι) ≅ CategoryTheory.Arrow.mk standardSq.ι
  refine CategoryTheory.Arrow.isoMk eLeft (e.app (B, T)).symm ?_
  change eLeft.hom ≫ standardSq.ι =
    L.map sq.ι ≫ ((pairedTensorIso F G L e).inv.app B).app T
  exact hι

omit [MonoidalCategory C] in
/-- Reduce generator-family pushout products to their original labelled arrows. -/
theorem generatorPair_pushoutProductLe [HasPushouts D]
    {S T : Type*} (F : S → C ⥤ D) (G : T → C ⥤ D)
    (P Q : MorphismProperty C) (W : MorphismProperty D)
    (hMaps : ∀ (a : S) (b : T) ⦃X Y K L : C⦄ (i : X ⟶ Y) (j : K ⟶ L),
      P i → Q j →
        W (CategoryTheory.Arrow.mk ((F a).map i) □ CategoryTheory.Arrow.mk ((G b).map j)).hom) :
    MorphismProperty.PushoutProductLe
      (MorphismProperty.adjointFamilyGenerators F P)
      (MorphismProperty.adjointFamilyGenerators G Q) W := by
  intro X Y K L i j hi hj
  obtain ⟨a, ha⟩ := (MorphismProperty.adjointFamilyGenerators_iff F P i).mp hi
  obtain ⟨b, hb⟩ := (MorphismProperty.adjointFamilyGenerators_iff G Q j).mp hj
  rw [ha, hb]
  exact hMaps a.1 b.1 a.2.1.hom b.2.1.hom a.2.2 b.2.2

omit [MonoidalCategory C] in
/-- Preserve a pushout-product property through equality of both complete input arrows. -/
theorem pushoutProduct_mem_of_pairArrow_eq [HasPushouts D]
    (W : MorphismProperty D) {X Y K L : D} (i : X ⟶ Y) (j : K ⟶ L)
    (a b : CategoryTheory.Arrow D)
    (ha : CategoryTheory.Arrow.mk i = a) (hb : CategoryTheory.Arrow.mk j = b)
    (h : W (a □ b).hom) :
    W (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom := by
  rw [ha, hb]
  exact h

end CategoryTheory.FreePairTransport
