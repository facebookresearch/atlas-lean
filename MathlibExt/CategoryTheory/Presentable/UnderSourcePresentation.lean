/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.FiniteSourceClosure
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The actual free-source pushout of an under-object

Every object under P is the pushout of its freely added underlying object
and the identity of P along the freely added P. The maps retain the actual
chosen point. This finite source presentation transfers preservation of a
selected cardinal-filtered colimit without a global presentability premise.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] {P : C}

set_option backward.isDefEq.respectTransparency false in
/-- Collapse the free copy of P to the original identity under-object. -/
@[no_expose]
def freePointCollapse : (costar P).obj P ⟶ mk (𝟙 P) :=
  homMk (coprod.desc (𝟙 P) (𝟙 P)) (by
    simp only [costar_obj_hom, coprod.inl_desc, mk_hom])

set_option backward.isDefEq.respectTransparency false in
/-- Forget the freely added point using the under-object's original chosen map. -/
@[no_expose]
def freeForgetCounit (A : Under P) : (costar P).obj A.right ⟶ A :=
  homMk (coprod.desc A.hom (𝟙 A.right)) (by
    simp only [costar_obj_hom, coprod.inl_desc])

set_option backward.isDefEq.respectTransparency false in
private theorem freeSourcePresentationIsPushout_private (A : Under P) :
    IsPushout ((costar P).map A.hom) freePointCollapse
      (freeForgetCounit A) (mkIdInitial.to A) := by
  have hsq : (costar P).map A.hom ≫ freeForgetCounit A =
      freePointCollapse ≫ mkIdInitial.to A := by
    apply UnderMorphism.ext
    simp only [Under.comp_right, mkIdInitial_to_right]
    change coprod.map (𝟙 P) A.hom ≫ coprod.desc A.hom (𝟙 A.right) =
      coprod.desc (𝟙 P) (𝟙 P) ≫ A.hom
    apply coprod.hom_ext <;> simp
  refine ⟨⟨hsq⟩, ⟨PushoutCocone.IsColimit.mk hsq ?_ ?_ ?_ ?_⟩⟩
  · intro s
    refine homMk (coprod.inr ≫ s.inl.right) ?_
    have hs := congrArg (fun f => coprod.inr ≫ f.right) s.condition
    change coprod.inr ≫ (coprod.map (𝟙 P) A.hom ≫ s.inl.right) =
      coprod.inr ≫ (coprod.desc (𝟙 P) (𝟙 P) ≫ s.inr.right) at hs
    simpa only [← Category.assoc, coprod.inr_map_assoc, coprod.inr_desc_assoc,
      Category.id_comp, Category.assoc, ← Under.w s.inr, mk_hom,
      Category.id_comp] using hs
  · intro s
    apply UnderMorphism.ext
    change coprod.desc A.hom (𝟙 A.right) ≫ (coprod.inr ≫ s.inl.right) = s.inl.right
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc]
      have hPoint : A.hom ≫ (coprod.inr ≫ s.inl.right) = s.pt.hom := by
        have hs := congrArg (fun f => coprod.inr ≫ f.right) s.condition
        change coprod.inr ≫ (coprod.map (𝟙 P) A.hom ≫ s.inl.right) =
          coprod.inr ≫ (coprod.desc (𝟙 P) (𝟙 P) ≫ s.inr.right) at hs
        simpa only [← Category.assoc, coprod.inr_map_assoc, coprod.inr_desc_assoc,
          Category.id_comp, Category.assoc, ← Under.w s.inr, mk_hom,
          Category.id_comp] using hs
      have hFree : coprod.inl ≫ s.inl.right = s.pt.hom := by
        simpa only [costar_obj_hom, coprod.inl_desc] using Under.w s.inl
      exact hPoint.trans hFree.symm
    · simp
  · intro s
    exact mkIdInitial.hom_ext _ _
  · intro s m hm _
    apply UnderMorphism.ext
    have h := congrArg (fun f => coprod.inr ≫ f.right) hm
    change coprod.inr ≫ (coprod.desc A.hom (𝟙 A.right) ≫ m.right) =
      coprod.inr ≫ s.inl.right at h
    simpa using h

/-- The original point and free copy exhibit every actual under-object as a pushout. -/
theorem freeSourcePresentationIsPushout (A : Under P) :
    IsPushout ((costar P).map A.hom) freePointCollapse
      (freeForgetCounit A) (mkIdInitial.to A) :=
  freeSourcePresentationIsPushout_private A

omit [HasBinaryCoproducts C] in
/-- The identity under-object is a source for every selected cardinal-filtered colimit. -/
theorem identitySource_preservesColimit
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
    (F : J ⥤ Under P) :
    PreservesColimit F (coyoneda.obj (Opposite.op (mk (𝟙 P)))) :=
  preservesColimit_coyoneda_of_finiteColimit κ F
    (asEmptyCocone (mk (𝟙 P))) mkIdInitial (fun k => k.as.elim)

/-- The actual free underlying source and free P source suffice for the original under-object. -/
theorem source_preservesColimit_of_costarSources
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
    (F : J ⥤ Under P) (A : Under P)
    (hPoint : PreservesColimit F
      (coyoneda.obj (Opposite.op ((costar P).obj P))))
    (hUnderlying : PreservesColimit F
      (coyoneda.obj (Opposite.op ((costar P).obj A.right)))) :
    PreservesColimit F (coyoneda.obj (Opposite.op A)) := by
  let h := freeSourcePresentationIsPushout A
  refine preservesColimit_coyoneda_of_finiteColimit κ F h.cocone h.isColimit ?_
  intro k
  cases k with
  | none => exact hPoint
  | some k =>
    cases k with
    | left => exact hUnderlying
    | right => exact identitySource_preservesColimit κ F

end CategoryTheory.Under
