/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Join
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Connected

/-!
# Basic properties of the join of simplicial sets

Properties of the simplicial join `X ⋆ Y` from the module
`MathlibExt.AlgebraicTopology.SimplicialSet.Join`, which is built by Day
convolution on augmented simplicial sets.

The main results landed in this file are:
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor ExternalProduct
  CategoryTheory.Prod

universe u v w

namespace SSet.Join

/-!
## External products and left Kan extensions
-/

/-- External product with a fixed left factor, as a functor in the right
factor. -/
@[simps]
def extProdLeft (F : AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :
    (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) ⥤
      ((AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ) ⥤ Type u) where
  obj G := F ⊠ G
  map α := (externalProductBifunctor AugmentedSimplexCategoryᵒᵖ
    AugmentedSimplexCategoryᵒᵖ (Type u)).map (𝟙 F ×ₘ α)

/-- External product with a fixed right factor, as a functor in the left
factor. -/
@[simps]
def extProdRight (F : AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :
    (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) ⥤
      ((AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ) ⥤ Type u) where
  obj G := G ⊠ F
  map α := (externalProductBifunctor AugmentedSimplexCategoryᵒᵖ
    AugmentedSimplexCategoryᵒᵖ (Type u)).map (α ×ₘ 𝟙 F)

/-- Left Kan extension along the tensor product of
`AugmentedSimplexCategoryᵒᵖ`, as a functor; this computes Day convolution. -/
abbrev dayLan :
    ((AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ) ⥤ Type u) ⥤
      (AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :=
  (tensor AugmentedSimplexCategoryᵒᵖ).lan

instance : dayLan.{u}.IsLeftAdjoint :=
  ⟨_, ⟨(tensor AugmentedSimplexCategoryᵒᵖ).lanAdjunction (Type u)⟩⟩

/-- Colimits in `DayCat`, transported from augmented simplicial sets along
the Day-functor equivalence. -/
instance {J : Type v} [Category.{w} J] [HasColimitsOfShape J (Type u)] :
    HasColimitsOfShape J DayCat.{u} :=
  Adjunction.hasColimitsOfShape_of_equivalence
    (MonoidalCategory.DayFunctor.equiv AugmentedSimplexCategoryᵒᵖ (Type u)).functor

section Colimits

variable {J : Type v} [Category.{w} J] [HasColimitsOfShape J (Type u)]

instance : PreservesColimitsOfShape J drop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape J
    ((Functor.whiskeringLeft _ _ _).obj AugmentedSimplexCategory.inclusion.op))

instance : PreservesColimitsOfShape J dropDay.{u} :=
  inferInstanceAs (PreservesColimitsOfShape J
    ((MonoidalCategory.DayFunctor.equiv _ _).functor ⋙ drop))

lemma extProdLeft_comp_evaluation (F : AugmentedSimplexCategoryᵒᵖ ⥤ Type u)
    (x y : AugmentedSimplexCategoryᵒᵖ) :
    extProdLeft F ⋙ (evaluation _ (Type u)).obj (x, y) =
      (evaluation _ (Type u)).obj y ⋙ tensorLeft (F.obj x) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro G G' α
  simp [extProdLeft]

lemma extProdRight_comp_evaluation (F : AugmentedSimplexCategoryᵒᵖ ⥤ Type u)
    (x y : AugmentedSimplexCategoryᵒᵖ) :
    extProdRight F ⋙ (evaluation _ (Type u)).obj (x, y) =
      (evaluation _ (Type u)).obj x ⋙ tensorRight (F.obj y) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro G G' α
  simp [extProdRight]

instance (F : AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :
    PreservesColimitsOfShape J (extProdLeft F) := by
  apply preservesColimitsOfShape_of_evaluation
  rintro ⟨x, y⟩
  rw [extProdLeft_comp_evaluation]
  infer_instance

instance (F : AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :
    PreservesColimitsOfShape J (extProdRight F) := by
  apply preservesColimitsOfShape_of_evaluation
  rintro ⟨x, y⟩
  rw [extProdRight_comp_evaluation]
  infer_instance

end Colimits

/-!
## Day tensoring as a left Kan extension
-/

/-- The underlying augmented simplicial set of a Day tensor product is the
left Kan extension computing Day convolution. -/
def dayTensorIsoLan (F G : DayCat.{u}) :
    (F ⊗ G).functor ≅ dayLan.obj (F.functor ⊠ G.functor) :=
  Functor.leftKanExtensionUnique (F ⊗ G).functor
    (MonoidalCategory.DayFunctor.η F G) _
    ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app (F.functor ⊠ G.functor))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma dayTensorIsoLan_η_hom_app (F G : DayCat.{u})
    (x y : AugmentedSimplexCategoryᵒᵖ) :
    (MonoidalCategory.DayFunctor.η F G).app (x, y) ≫
        (dayTensorIsoLan F G).hom.app (x ⊗ y) =
      ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app
        (F.functor ⊠ G.functor)).app (x, y) := by
  have h := Functor.descOfIsLeftKanExtension_fac_app (F ⊗ G).functor
    (MonoidalCategory.DayFunctor.η F G) (dayLan.obj (F.functor ⊠ G.functor))
    ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app (F.functor ⊠ G.functor)) (x, y)
  simpa [dayTensorIsoLan, Functor.leftKanExtensionUnique] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma lanUnit_app_map_extProdLeft_app (F G G' : DayCat.{u}) (α : G ⟶ G')
    (x y : AugmentedSimplexCategoryᵒᵖ) :
    ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app (F.functor ⊠ G.functor)).app
        (x, y) ≫
      (dayLan.map ((extProdLeft F.functor).map α.natTrans)).app (x ⊗ y) =
    (F.functor.obj x ◁ α.natTrans.app y) ≫
      ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app
        (F.functor ⊠ G'.functor)).app (x, y) := by
  have hnat := NatTrans.congr_app
    ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.naturality
      ((extProdLeft F.functor).map α.natTrans)) (x, y)
  simp [extProdLeft] at hnat
  simpa [extProdLeft] using hnat.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma lanUnit_app_map_extProdRight_app (F G G' : DayCat.{u}) (α : G ⟶ G')
    (x y : AugmentedSimplexCategoryᵒᵖ) :
    ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app (G.functor ⊠ F.functor)).app
        (x, y) ≫
      (dayLan.map ((extProdRight F.functor).map α.natTrans)).app (x ⊗ y) =
    (α.natTrans.app x ▷ F.functor.obj y) ≫
      ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app
        (G'.functor ⊠ F.functor)).app (x, y) := by
  have hnat := NatTrans.congr_app
    ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.naturality
      ((extProdRight F.functor).map α.natTrans)) (x, y)
  simp [extProdRight] at hnat
  simpa [extProdRight] using hnat.symm

lemma η_whiskerLeft_app (F G G' : DayCat.{u}) (α : G ⟶ G')
    (x y : AugmentedSimplexCategoryᵒᵖ) :
    (MonoidalCategory.DayFunctor.η F G).app (x, y) ≫
        (F ◁ α).natTrans.app (x ⊗ y) =
      (F.functor.obj x ◁ α.natTrans.app y) ≫
        (MonoidalCategory.DayFunctor.η F G').app (x, y) :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
    (Type u) F α x y

lemma η_whiskerRight_app (F F' G : DayCat.{u}) (α : F ⟶ F')
    (x y : AugmentedSimplexCategoryᵒᵖ) :
    (MonoidalCategory.DayFunctor.η F G).app (x, y) ≫
        (α ▷ G).natTrans.app (x ⊗ y) =
      (α.natTrans.app x ▷ G.functor.obj y) ≫
        (MonoidalCategory.DayFunctor.η F' G).app (x, y) :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
    AugmentedSimplexCategoryᵒᵖ (Type u) α G x y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Tensoring on the left in `DayCat`, after forgetting to augmented
simplicial sets, is external product followed by left Kan extension. -/
def tensorLeftCompDayEquivIso (F : DayCat.{u}) :
    tensorLeft F ⋙ (MonoidalCategory.DayFunctor.equiv _ _).functor ≅
      (MonoidalCategory.DayFunctor.equiv _ _).functor ⋙ extProdLeft F.functor ⋙
        dayLan :=
  NatIso.ofComponents (fun G => dayTensorIsoLan F G) (by
    intro G G' α
    apply Functor.hom_ext_of_isLeftKanExtension (F ⊗ G).functor
      (MonoidalCategory.DayFunctor.η F G) _
    apply CategoryTheory.NatTrans.ext
    funext ⟨x, y⟩
    have key1 : (MonoidalCategory.DayFunctor.η F G).app (x, y) ≫
          (F ◁ α).natTrans.app (x ⊗ y) ≫ (dayTensorIsoLan F G').hom.app (x ⊗ y) =
        (F.functor.obj x ◁ α.natTrans.app y) ≫
          ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app
            (F.functor ⊠ G'.functor)).app (x, y) := by
      rw [← Category.assoc, η_whiskerLeft_app, Category.assoc,
        dayTensorIsoLan_η_hom_app]
    have key2 : (MonoidalCategory.DayFunctor.η F G).app (x, y) ≫
          (dayTensorIsoLan F G).hom.app (x ⊗ y) ≫
            (dayLan.map ((extProdLeft F.functor).map α.natTrans)).app (x ⊗ y) =
        (F.functor.obj x ◁ α.natTrans.app y) ≫
          ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app
            (F.functor ⊠ G'.functor)).app (x, y) := by
      rw [← Category.assoc, dayTensorIsoLan_η_hom_app,
        lanUnit_app_map_extProdLeft_app]
    change (MonoidalCategory.DayFunctor.η F G).app (x, y) ≫
          (F ◁ α).natTrans.app (x ⊗ y) ≫ (dayTensorIsoLan F G').hom.app (x ⊗ y) =
        (MonoidalCategory.DayFunctor.η F G).app (x, y) ≫
          (dayTensorIsoLan F G).hom.app (x ⊗ y) ≫
            (dayLan.map ((extProdLeft F.functor).map α.natTrans)).app (x ⊗ y)
    exact key1.trans key2.symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Tensoring on the right in `DayCat`, after forgetting to augmented
simplicial sets, is external product followed by left Kan extension. -/
def tensorRightCompDayEquivIso (F : DayCat.{u}) :
    tensorRight F ⋙ (MonoidalCategory.DayFunctor.equiv _ _).functor ≅
      (MonoidalCategory.DayFunctor.equiv _ _).functor ⋙ extProdRight F.functor ⋙
        dayLan :=
  NatIso.ofComponents (fun G => dayTensorIsoLan G F) (by
    intro G G' α
    apply Functor.hom_ext_of_isLeftKanExtension (G ⊗ F).functor
      (MonoidalCategory.DayFunctor.η G F) _
    apply CategoryTheory.NatTrans.ext
    funext ⟨x, y⟩
    have key1 : (MonoidalCategory.DayFunctor.η G F).app (x, y) ≫
          (α ▷ F).natTrans.app (x ⊗ y) ≫ (dayTensorIsoLan G' F).hom.app (x ⊗ y) =
        (α.natTrans.app x ▷ F.functor.obj y) ≫
          ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app
            (G'.functor ⊠ F.functor)).app (x, y) := by
      rw [← Category.assoc, η_whiskerRight_app, Category.assoc,
        dayTensorIsoLan_η_hom_app]
    have key2 : (MonoidalCategory.DayFunctor.η G F).app (x, y) ≫
          (dayTensorIsoLan G F).hom.app (x ⊗ y) ≫
            (dayLan.map ((extProdRight F.functor).map α.natTrans)).app (x ⊗ y) =
        (α.natTrans.app x ▷ F.functor.obj y) ≫
          ((tensor AugmentedSimplexCategoryᵒᵖ).lanUnit.app
            (G'.functor ⊠ F.functor)).app (x, y) := by
      rw [← Category.assoc, dayTensorIsoLan_η_hom_app,
        lanUnit_app_map_extProdRight_app]
    change (MonoidalCategory.DayFunctor.η G F).app (x, y) ≫
          (α ▷ F).natTrans.app (x ⊗ y) ≫ (dayTensorIsoLan G' F).hom.app (x ⊗ y) =
        (MonoidalCategory.DayFunctor.η G F).app (x, y) ≫
          (dayTensorIsoLan G F).hom.app (x ⊗ y) ≫
            (dayLan.map ((extProdRight F.functor).map α.natTrans)).app (x ⊗ y)
    exact key1.trans key2.symm)

section Colimits

variable {J : Type v} [Category.{w} J] [HasColimitsOfShape J (Type u)]

instance (F : DayCat.{u}) : PreservesColimitsOfShape J (tensorLeft F) := by
  have hcomp : PreservesColimitsOfShape J
      (tensorLeft F ⋙ (MonoidalCategory.DayFunctor.equiv _ _).functor) :=
    preservesColimitsOfShape_of_natIso (tensorLeftCompDayEquivIso F).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (tensorLeft F)
    (MonoidalCategory.DayFunctor.equiv _ _).functor

instance (F : DayCat.{u}) : PreservesColimitsOfShape J (tensorRight F) := by
  have hcomp : PreservesColimitsOfShape J
      (tensorRight F ⋙ (MonoidalCategory.DayFunctor.equiv _ _).functor) :=
    preservesColimitsOfShape_of_natIso (tensorRightCompDayEquivIso F).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (tensorRight F)
    (MonoidalCategory.DayFunctor.equiv _ _).functor

end Colimits

/-!
## Augmentation preserves connected colimits
-/

section ConnectedColimits

variable {J : Type v} [Category.{w} J] [HasColimitsOfShape J (Type u)]

lemma aug_comp_evaluation_of (n : SimplexCategory) :
    aug.{u} ⋙ (evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
        (Opposite.op (WithInitial.of n)) =
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op n) :=
  rfl

lemma aug_comp_evaluation_star :
    aug.{u} ⋙ (evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
        (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) =
      (Functor.const SSet.{u}).obj (PUnit : Type u) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
    evaluation_obj_map, Functor.const_obj_map]
  apply Types.isTerminalPUnit.hom_ext

omit [HasColimitsOfShape J (Type u)] in
/-- The constant functor at a one-point type preserves any colimit indexed
by a connected category. -/
lemma preservesColimit_const_punit [IsConnected J] (K : J ⥤ SSet.{u}) :
    PreservesColimit K ((Functor.const SSet.{u}).obj (PUnit : Type u)) := by
  refine ⟨fun {c} _ => ⟨?_⟩⟩
  exact Limits.Types.isColimitPUnitCocone J

/-- Augmentation preserves colimits indexed by a connected category: away
from degree `-1` this is evaluation, and in degree `-1` both sides are a
one-point type. -/
instance [IsConnected J] : PreservesColimitsOfShape J aug.{u} := by
  apply preservesColimitsOfShape_of_evaluation
  intro x
  obtain ⟨a, rfl⟩ : ∃ a, x = Opposite.op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      rw [aug_comp_evaluation_of]
      infer_instance
  | star =>
      rw [aug_comp_evaluation_star]
      exact ⟨fun {K} => preservesColimit_const_punit K⟩

instance [IsConnected J] : PreservesColimitsOfShape J augDay.{u} :=
  inferInstanceAs (PreservesColimitsOfShape J
    (aug ⋙ (MonoidalCategory.DayFunctor.equiv _ _).inverse))

end ConnectedColimits

end SSet.Join

namespace SSet

/-!
## The join preserves connected colimits
-/

/-- The join with fixed left factor, as a composite through `DayCat`. -/
lemma join_obj_eq_comp (X : SSet.{u}) :
    join.obj X =
      Join.augDay ⋙ tensorLeft (Join.augDay.obj X) ⋙ Join.dropDay := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro Y Z f
  dsimp only [SSet.join, Functor.curryObj]
  simp

/-- The join with fixed right factor, as a composite through `DayCat`. -/
lemma join_flip_obj_eq_comp (Y : SSet.{u}) :
    join.flip.obj Y =
      Join.augDay ⋙ tensorRight (Join.augDay.obj Y) ⋙ Join.dropDay := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Z f
  dsimp only [SSet.join, Functor.curryObj, Functor.flip]
  simp

section ConnectedColimits

variable {J : Type v} [Category.{w} J] [HasColimitsOfShape J (Type u)]
  [IsConnected J]

/-- The join preserves connected colimits in the right variable; in
particular it preserves coequalizers and pushouts in the right variable. -/
instance (X : SSet.{u}) : PreservesColimitsOfShape J (join.obj X) := by
  rw [join_obj_eq_comp]
  infer_instance

/-- The join preserves connected colimits in the left variable; in
particular it preserves coequalizers and pushouts in the left variable. -/
instance (Y : SSet.{u}) : PreservesColimitsOfShape J (join.flip.obj Y) := by
  rw [join_flip_obj_eq_comp]
  infer_instance

end ConnectedColimits

/-- The join preserves filtered colimits in the right variable. -/
theorem preservesColimitsOfShape_join_obj_of_isFiltered
    {J : Type v} [SmallCategory J] [HasColimitsOfShape J (Type u)]
    [IsFiltered J] (X : SSet.{u}) :
    PreservesColimitsOfShape J (join.obj X) := by
  have : IsConnected J := IsFiltered.isConnected J
  infer_instance

/-- The join preserves filtered colimits in the left variable. -/
theorem preservesColimitsOfShape_join_flip_obj_of_isFiltered
    {J : Type v} [SmallCategory J] [HasColimitsOfShape J (Type u)]
    [IsFiltered J] (Y : SSet.{u}) :
    PreservesColimitsOfShape J (join.flip.obj Y) := by
  have : IsConnected J := IsFiltered.isConnected J
  infer_instance

/-!
## Canonical inclusions
-/

/-- The canonical inclusion of the left factor into a join, obtained from
the right unit isomorphism by mapping along the unique map out of the empty
simplicial set. -/
def joinInl (X Y : SSet.{u}) : X ⟶ X ⋆ Y :=
  (joinBotIso X).inv ≫ (join.obj X).map (initial.to Y)

/-- The canonical inclusion of the right factor into a join, obtained from
the left unit isomorphism by mapping along the unique map out of the empty
simplicial set. -/
def joinInr (X Y : SSet.{u}) : Y ⟶ X ⋆ Y :=
  (botJoinIso Y).inv ≫ (join.map (initial.to X)).app Y

@[simp]
lemma joinInl_bot (X : SSet.{u}) : joinInl X (⊥_ SSet.{u}) = (joinBotIso X).inv := by
  simp only [joinInl]
  rw [show initial.to (⊥_ SSet.{u}) = 𝟙 (⊥_ SSet.{u}) from
    initialIsInitial.hom_ext _ _]
  simp

@[simp]
lemma joinInr_bot (Y : SSet.{u}) : joinInr (⊥_ SSet.{u}) Y = (botJoinIso Y).inv := by
  simp only [joinInr]
  rw [show initial.to (⊥_ SSet.{u}) = 𝟙 (⊥_ SSet.{u}) from
    initialIsInitial.hom_ext _ _]
  simp

/-- The left inclusion is natural in the right variable. -/
lemma joinInl_comp_map {Y Y' : SSet.{u}} (X : SSet.{u}) (g : Y ⟶ Y') :
    joinInl X Y ≫ (join.obj X).map g = joinInl X Y' := by
  simp only [joinInl, Category.assoc, ← Functor.map_comp]
  rw [show initial.to Y ≫ g = initial.to Y' from initialIsInitial.hom_ext _ _]

/-- The right inclusion is natural in the left variable. -/
lemma joinInr_comp_map {X X' : SSet.{u}} (f : X ⟶ X') (Y : SSet.{u}) :
    joinInr X Y ≫ (join.map f).app Y = joinInr X' Y := by
  simp only [joinInr, Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
  rw [show initial.to X ≫ f = initial.to X' from initialIsInitial.hom_ext _ _]

lemma dropDay_map_augDay_map {X X' : SSet.{u}} (f : X ⟶ X') :
    Join.dropDay.map (Join.augDay.map f) = f :=
  rfl

lemma join_map_app_bot_eq {X X' : SSet.{u}} (f : X ⟶ X') :
    (join.map f).app (⊥_ SSet.{u}) =
      Join.dropDay.map (Join.augDay.map f ▷ Join.augDay.obj (⊥_ SSet.{u})) := by
  dsimp only [SSet.join, Functor.curryObj]
  simp

lemma join_obj_bot_map_eq {Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    (join.obj (⊥_ SSet.{u})).map g =
      Join.dropDay.map (Join.augDay.obj (⊥_ SSet.{u}) ◁ Join.augDay.map g) := by
  dsimp only [SSet.join, Functor.curryObj]
  simp

/-- Naturality of the right unit isomorphism for the join. -/
lemma joinBotIso_naturality {X X' : SSet.{u}} (f : X ⟶ X') :
    (join.map f).app (⊥_ SSet.{u}) ≫ (joinBotIso X').hom =
      (joinBotIso X).hom ≫ f := by
  rw [join_map_app_bot_eq]
  change Join.dropDay.map (Join.augDay.map f ▷ Join.augDay.obj (⊥_ SSet.{u})) ≫
      Join.dropDay.map (MonoidalCategory.tensorIso (Iso.refl (Join.augDay.obj X'))
          Join.augDayBotIso ≪≫
        MonoidalCategory.tensorIso (Iso.refl (Join.augDay.obj X'))
          Join.dayUnitYonedaIso.symm ≪≫
        ρ_ (Join.augDay.obj X')).hom =
    Join.dropDay.map (MonoidalCategory.tensorIso (Iso.refl (Join.augDay.obj X))
          Join.augDayBotIso ≪≫
        MonoidalCategory.tensorIso (Iso.refl (Join.augDay.obj X))
          Join.dayUnitYonedaIso.symm ≪≫
        ρ_ (Join.augDay.obj X)).hom ≫
      Join.dropDay.map (Join.augDay.map f)
  rw [← Join.dropDay.map_comp, ← Join.dropDay.map_comp]
  congr 1
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom, Iso.refl_hom,
    Iso.symm_hom, Category.assoc]
  rw [← MonoidalCategory.rightUnitor_naturality]
  simp only [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id,
    Category.id_comp]

/-- Naturality of the left unit isomorphism for the join. -/
lemma botJoinIso_naturality {Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    (join.obj (⊥_ SSet.{u})).map g ≫ (botJoinIso Y').hom =
      (botJoinIso Y).hom ≫ g := by
  rw [join_obj_bot_map_eq]
  change Join.dropDay.map (Join.augDay.obj (⊥_ SSet.{u}) ◁ Join.augDay.map g) ≫
      Join.dropDay.map (MonoidalCategory.tensorIso Join.augDayBotIso
          (Iso.refl (Join.augDay.obj Y')) ≪≫
        MonoidalCategory.tensorIso Join.dayUnitYonedaIso.symm
          (Iso.refl (Join.augDay.obj Y')) ≪≫
        λ_ (Join.augDay.obj Y')).hom =
    Join.dropDay.map (MonoidalCategory.tensorIso Join.augDayBotIso
          (Iso.refl (Join.augDay.obj Y)) ≪≫
        MonoidalCategory.tensorIso Join.dayUnitYonedaIso.symm
          (Iso.refl (Join.augDay.obj Y)) ≪≫
        λ_ (Join.augDay.obj Y)).hom ≫
      Join.dropDay.map (Join.augDay.map g)
  rw [← Join.dropDay.map_comp, ← Join.dropDay.map_comp]
  congr 1
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom, Iso.refl_hom,
    Iso.symm_hom, Category.assoc]
  rw [← MonoidalCategory.leftUnitor_naturality]
  simp only [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id,
    Category.id_comp]

/-- The left inclusion is natural in the left variable. -/
lemma map_comp_joinInl {X X' : SSet.{u}} (f : X ⟶ X') (Y : SSet.{u}) :
    f ≫ joinInl X' Y = joinInl X Y ≫ (join.map f).app Y := by
  have hnat : f ≫ (joinBotIso X').inv =
      (joinBotIso X).inv ≫ (join.map f).app (⊥_ SSet.{u}) := by
    apply (cancel_mono (joinBotIso X').hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [joinBotIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hinter : (join.map f).app (⊥_ SSet.{u}) ≫ (join.obj X').map (initial.to Y) =
      (join.obj X).map (initial.to Y) ≫ (join.map f).app Y :=
    ((join.map f).naturality (initial.to Y)).symm
  calc f ≫ joinInl X' Y
      = (f ≫ (joinBotIso X').inv) ≫ (join.obj X').map (initial.to Y) := by
        simp only [joinInl, Category.assoc]
    _ = ((joinBotIso X).inv ≫ (join.map f).app (⊥_ SSet.{u})) ≫
          (join.obj X').map (initial.to Y) := by rw [hnat]
    _ = (joinBotIso X).inv ≫ ((join.map f).app (⊥_ SSet.{u}) ≫
          (join.obj X').map (initial.to Y)) := by rw [Category.assoc]
    _ = (joinBotIso X).inv ≫ ((join.obj X).map (initial.to Y) ≫
          (join.map f).app Y) := by rw [hinter]
    _ = joinInl X Y ≫ (join.map f).app Y := by simp only [joinInl, Category.assoc]

/-- The right inclusion is natural in the right variable. -/
lemma map_comp_joinInr {Y Y' : SSet.{u}} (g : Y ⟶ Y') (X : SSet.{u}) :
    g ≫ joinInr X Y' = joinInr X Y ≫ (join.obj X).map g := by
  have hnat : g ≫ (botJoinIso Y').inv =
      (botJoinIso Y).inv ≫ (join.obj (⊥_ SSet.{u})).map g := by
    apply (cancel_mono (botJoinIso Y').hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [botJoinIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hinter : (join.obj (⊥_ SSet.{u})).map g ≫
        (join.map (initial.to X)).app Y' =
      (join.map (initial.to X)).app Y ≫ (join.obj X).map g :=
    (join.map (initial.to X)).naturality g
  calc g ≫ joinInr X Y'
      = (g ≫ (botJoinIso Y').inv) ≫ (join.map (initial.to X)).app Y' := by
        simp only [joinInr, Category.assoc]
    _ = ((botJoinIso Y).inv ≫ (join.obj (⊥_ SSet.{u})).map g) ≫
          (join.map (initial.to X)).app Y' := by rw [hnat]
    _ = (botJoinIso Y).inv ≫ ((join.obj (⊥_ SSet.{u})).map g ≫
          (join.map (initial.to X)).app Y') := by rw [Category.assoc]
    _ = (botJoinIso Y).inv ≫ ((join.map (initial.to X)).app Y ≫
          (join.obj X).map g) := by rw [hinter]
    _ = joinInr X Y ≫ (join.obj X).map g := by simp only [joinInr, Category.assoc]

/-!
## The join does not preserve initial objects
-/

lemma not_isInitial_stdSimplex_zero : IsInitial (Δ[0] : SSet.{u}) → False := by
  intro h
  have h0 := h.isInitialObj
    ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))
  cases (h0.to (PEmpty.{u + 1} : Type u) (SSet.stdSimplex.obj₀Equiv (n := 0) |>.symm 0))

/-- `Δ[0] ⋆ ⊥` is not initial: joining does not preserve initial objects
(hence not all colimits, and not coproducts) in either variable. -/
theorem not_isInitial_joinBot_one : IsInitial (Δ[0] ⋆ (⊥_ SSet.{u})) → False :=
  fun h => not_isInitial_stdSimplex_zero (h.ofIso (SSet.joinBotIso Δ[0]))

/-- `⊥ ⋆ Δ[0]` is not initial: the other variable of
`not_isInitial_joinBot_one`. -/
theorem not_isInitial_botJoin_one : IsInitial ((⊥_ SSet.{u}) ⋆ Δ[0]) → False :=
  fun h => not_isInitial_stdSimplex_zero (h.ofIso (SSet.botJoinIso Δ[0]))

end SSet

namespace SSet.Join

/-!
## Associativity
-/

/-- The object of `CostructuredArrow (tensor AugmentedSimplexCategoryᵒᵖ)
(op star)` given by the pair `(star, star)`; it is terminal, since maps
into `op star` in `AugmentedSimplexCategoryᵒᵖ` are unique. -/
def costructuredArrowStarObj :
    CostructuredArrow (tensor AugmentedSimplexCategoryᵒᵖ)
      (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) :=
  CostructuredArrow.mk (Y := (Opposite.op (WithInitial.star :
    AugmentedSimplexCategory), Opposite.op (WithInitial.star :
      AugmentedSimplexCategory))) (𝟙 _)

/-- The pair `(star, star)` is a terminal object of the costructured-arrow
category over `op star`: maps into `op star` in
`AugmentedSimplexCategoryᵒᵖ` are unique. -/
def isTerminalCostructuredArrowStarObj : IsTerminal costructuredArrowStarObj := by
  have eq_to_op_star : ∀ {x : AugmentedSimplexCategoryᵒᵖ}
      (p q : x ⟶ Opposite.op (WithInitial.star : AugmentedSimplexCategory)), p = q := by
    intro x p q
    have h : p.unop = q.unop := WithInitial.starInitial.hom_ext _ _
    rw [← Quiver.Hom.op_unop p, ← Quiver.Hom.op_unop q, h]
  refine IsTerminal.ofUniqueHom (fun t => CostructuredArrow.homMk
    ((WithInitial.starInitial.to t.left.1.unop).op ×ₘ
      (WithInitial.starInitial.to t.left.2.unop).op) (by
      apply eq_to_op_star)) (fun t a => ?_)
  apply CostructuredArrow.hom_ext
  apply Prod.ext
  · apply eq_to_op_star
  · apply eq_to_op_star

/-- The monoidal tensor product of two terminal objects of `Type u` is
terminal. -/
def isTerminalTensorTypes {A B : Type u} (hA : IsTerminal A) (hB : IsTerminal B) :
    IsTerminal (A ⊗ B) :=
  Types.isTerminalPUnit.ofIso
    (MonoidalCategory.tensorIso (hA.uniqueUpToIso Types.isTerminalPUnit)
      (hB.uniqueUpToIso Types.isTerminalPUnit) ≪≫ λ_ (PUnit : Type u)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degree `-1` part of a Day tensor product of augmented simplicial
sets with terminal degree `-1` part is again terminal: the indexing
category for the pointwise Kan extension at `star` has a terminal object. -/
def isTerminalDayTensorFunctorObjStar (F G : DayCat.{u})
    (hF : IsTerminal (F.functor.obj
      (Opposite.op (WithInitial.star : AugmentedSimplexCategory))))
    (hG : IsTerminal (G.functor.obj
      (Opposite.op (WithInitial.star : AugmentedSimplexCategory)))) :
    IsTerminal ((F ⊗ G).functor.obj
      (Opposite.op (WithInitial.star : AugmentedSimplexCategory))) := by
  have h : (Functor.LeftExtension.mk (F ⊗ G).functor
        (MonoidalCategory.DayFunctor.η F G)).IsPointwiseLeftKanExtensionAt
      (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) :=
    open LawfulDayConvolutionMonoidalCategoryStruct in
    isPointwiseLeftKanExtensionConvolutionExtensionUnit
      F G (Opposite.op (WithInitial.star : AugmentedSimplexCategory))
  haveI : HasColimit (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ)
      (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) ⋙
        (F.functor ⊠ G.functor)) :=
    h.hasPointwiseLeftKanExtensionAt
  have iso1 : (F ⊗ G).functor.obj
        (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) ≅
      colimit (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ)
        (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) ⋙
          (F.functor ⊠ G.functor)) :=
    h.isoColimit
  have hTip : IsTerminal ((CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ)
        (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) ⋙
          (F.functor ⊠ G.functor)).obj costructuredArrowStarObj) := by
    change IsTerminal (F.functor.obj
        (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) ⊗
      G.functor.obj (Opposite.op (WithInitial.star : AugmentedSimplexCategory)))
    exact isTerminalTensorTypes hF hG
  have iso2 : colimit (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ)
        (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) ⋙
          (F.functor ⊠ G.functor)) ≅
      (CostructuredArrow.proj (tensor AugmentedSimplexCategoryᵒᵖ)
        (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) ⋙
          (F.functor ⊠ G.functor)).obj costructuredArrowStarObj :=
    (colimit.isColimit _).coconePointUniqueUpToIso
      (colimitOfDiagramTerminal isTerminalCostructuredArrowStarObj _)
  exact hTip.ofIso (iso1 ≪≫ iso2).symm

/-- An augmented simplicial set with terminal degree `-1` part is the
augmentation of its underlying simplicial set. -/
def augDropIsoOfIsTerminalStar (H : AugmentedSimplexCategoryᵒᵖ ⥤ Type u)
    (hH : IsTerminal (H.obj
      (Opposite.op (WithInitial.star : AugmentedSimplexCategory)))) :
    aug.obj (drop.obj H) ≅ H :=
  NatIso.ofComponents
    (fun x => WithInitial.rec
      (motive := fun a => (aug.obj (drop.obj H)).obj (Opposite.op a) ≅
        H.obj (Opposite.op a))
      (fun _ => Iso.refl _)
      (Types.isTerminalPUnit.uniqueUpToIso hH)
      x.unop)
    (by
      intro x y f
      obtain ⟨a, rfl⟩ : ∃ a, x = Opposite.op a := ⟨x.unop, rfl⟩
      obtain ⟨b, rfl⟩ : ∃ b, y = Opposite.op b := ⟨y.unop, rfl⟩
      cases a with
      | of m =>
          cases b with
          | of k =>
              ext e
              rfl
          | star => apply hH.hom_ext
      | star =>
          cases b with
          | of k => exact (WithInitial.false_of_to_star f.unop).elim
          | star => apply hH.hom_ext)

/-- Augmentation is compatible with Day tensor products on augmented
extensions of simplicial sets: `augDay` of a join is the Day tensor of the
augmentations. -/
def augDayJoinIso (X Y : SSet.{u}) :
    augDay.obj (X ⋆ Y) ≅ augDay.obj X ⊗ augDay.obj Y :=
  (MonoidalCategory.DayFunctor.equiv _ _).inverse.mapIso
    (augDropIsoOfIsTerminalStar (augDay.obj X ⊗ augDay.obj Y).functor
      (isTerminalDayTensorFunctorObjStar _ _
        (by
          rw [augDay_obj_functor, aug_obj_obj_star]
          exact Types.isTerminalPUnit)
        (by
          rw [augDay_obj_functor, aug_obj_obj_star]
          exact Types.isTerminalPUnit)))

/-!
## Augmentation preserves monomorphisms
-/

/-- Augmentation preserves monomorphisms: this is checked degree by
degree, using monomorphy in positive degrees and subsingularity in
degree `-1`. Preservation of monomorphisms by the join itself is not
landed; see the file header for the blocker. -/
lemma aug_map_mono {X Y : SSet.{u}} {f : X ⟶ Y} [Mono f] : Mono (aug.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro x
  obtain ⟨a, rfl⟩ : ∃ a, x = Opposite.op a := ⟨x.unop, rfl⟩
  cases a with
  | of n =>
      exact (NatTrans.mono_iff_mono_app f).mp inferInstance _
  | star =>
      have happ : (aug.map f).app
            (Opposite.op (WithInitial.star : AugmentedSimplexCategory)) =
          𝟙 (PUnit : Type u) := Types.isTerminalPUnit.hom_ext _ _
      rw [happ]
      exact (mono_iff_injective _).2 Function.injective_id

end SSet.Join

namespace SSet

/-- Associativity of the join, from the Day associator in `DayCat`
transported along `Join.augDayJoinIso`. -/
def joinAssocIso (X Y Z : SSet.{u}) : (X ⋆ Y) ⋆ Z ≅ X ⋆ (Y ⋆ Z) :=
  Join.dropDay.mapIso
    (MonoidalCategory.tensorIso (Join.augDayJoinIso X Y) (Iso.refl _) ≪≫
      α_ _ _ _ ≪≫
        MonoidalCategory.tensorIso (Iso.refl _) (Join.augDayJoinIso Y Z).symm)

end SSet

/-!
## Naturality of `joinStdSimplexIso` and `joinInl` on representables

The join bifunctor is `dropDay` of the Day tensor of augmented
extensions, so its maps are `dropDay.map` of whiskered Day maps;
on representables, `dayTensorYonedaIso` is natural because
`yonedaTensorNatTrans` is (it is tensoring of homs in the
augmented simplex category), and `augDayStdSimplexIso` is natural
because its components are the identity away from degree `-1`
and forced in degree `-1`. Composing gives naturality of
`joinStdSimplexIso` in the left variable
(`SSet.joinStdSimplexIso_natural_left`). The Yoneda-element
chase through the Day right unitor then identifies the left
endpoint inclusion on representables
(`SSet.joinInl_comp_joinStdSimplexIso_hom`).
-/

namespace SSet

/-- The map of two joins induced by a map in the left variable is
`dropDay.map` of the whiskered augmented map. (General-Y form of
`SSet.join_map_app_bot_eq`.) -/
lemma join_map_app_eq {X X' Y : SSet.{u}} (f : X ⟶ X') :
    (join.map f).app Y =
      Join.dropDay.map (Join.augDay.map f ▷ Join.augDay.obj Y) := by
  dsimp only [SSet.join, Functor.curryObj]
  simp

/-- The map of two joins induced by a map in the right variable
is `dropDay.map` of the whiskered augmented map. (General-X form
of `SSet.join_obj_bot_map_eq`.) -/
lemma join_obj_map_eq {Y Y' : SSet.{u}} (X : SSet.{u}) (g : Y ⟶ Y') :
    (join.obj X).map g =
      Join.dropDay.map (Join.augDay.obj X ◁ Join.augDay.map g) := by
  dsimp only [SSet.join, Functor.curryObj]
  simp

namespace Join

/-- The morphism of augmented representables in `DayCat` induced
by a morphism `α : a ⟶ b` of the augmented simplex category. -/
def dayYonedaMap {a b : AugmentedSimplexCategory} (α : a ⟶ b) :
    dayYoneda.{u} a ⟶ dayYoneda.{u} b :=
  ⟨uliftYoneda.map α⟩

@[simp]
lemma dayYonedaMap_natTrans {a b : AugmentedSimplexCategory}
    (α : a ⟶ b) :
    (dayYonedaMap.{u} α).natTrans = uliftYoneda.map α :=
  rfl

/-- `dayYonedaMap` preserves identities. -/
lemma dayYonedaMap_id (a : AugmentedSimplexCategory) :
    dayYonedaMap.{u} (𝟙 a) = 𝟙 (dayYoneda.{u} a) := by
  apply DayFunctor.hom_ext
  simp [dayYonedaMap_natTrans]

/-- A hom of the simplex category, read as a hom of the
augmented simplex category between the corresponding `of`
objects. This is `AugmentedSimplexCategory.inclusion.map φ`,
with the type ascribed so that `WithInitial.of` appears
syntactically. -/
abbrev ofHom {m m' : ℕ} (φ : ⦋m⦌ ⟶ ⦋m'⦌) :
    (WithInitial.of ⦋m⦌ : AugmentedSimplexCategory) ⟶
      WithInitial.of ⦋m'⦌ :=
  AugmentedSimplexCategory.inclusion.map φ

/-- **Naturality of `dayTensorYonedaIso`**: tensoring homs of
augmented representables and then applying
`dayTensorYonedaIso` equals applying `dayTensorYonedaIso` and
then the representable map of the tensored hom. The proof is
`DayFunctor.tensor_hom_ext` followed by the `η`-whisker lemmas
of `JoinProperties.lean`; on elements both sides send
`(up f, up g)` to `up ((f ≫ α) ⊗ₘ (g ≫ β)) = up ((f ⊗ₘ g) ≫
(α ⊗ₘ β))`. -/
theorem dayTensorYonedaIso_natural {a a' b b' : AugmentedSimplexCategory}
    (α : a ⟶ a') (β : b ⟶ b') :
    (dayYonedaMap.{u} α ⊗ₘ dayYonedaMap.{u} β) ≫
        (dayTensorYonedaIso a' b').hom =
      (dayTensorYonedaIso a b).hom ≫ dayYonedaMap.{u} (α ⊗ₘ β) := by
  apply DayFunctor.tensor_hom_ext
  intro x y
  have htensor : (dayYonedaMap.{u} α ⊗ₘ dayYonedaMap.{u} β) =
      (dayYonedaMap.{u} α ▷ dayYoneda.{u} b) ≫
        (dayYoneda.{u} a' ◁ dayYonedaMap.{u} β) :=
    MonoidalCategory.tensorHom_def _ _
  apply TypeCat.homEquiv.injective
  funext ⟨⟨f⟩, ⟨g⟩⟩
  have hmap : ∀ {c d : AugmentedSimplexCategory} (γ : c ⟶ d)
      (z : AugmentedSimplexCategoryᵒᵖ) (h : z.unop ⟶ c),
      (uliftYoneda.map γ).app z (ULift.up h) = ULift.up (h ≫ γ) := by
    intro c d γ z h
    rfl
  have hstep1 : (dayYonedaMap.{u} α ▷ dayYoneda.{u} b).natTrans.app (x ⊗ y)
        ((DayFunctor.η (dayYoneda.{u} a) (dayYoneda.{u} b)).app (x, y)
          (ULift.up f, ULift.up g)) =
      (DayFunctor.η (dayYoneda.{u} a') (dayYoneda.{u} b)).app (x, y)
        (ULift.up (f ≫ α), ULift.up g) := by
    have h := types_congr_hom
      (η_whiskerRight_app (dayYoneda.{u} a) (dayYoneda.{u} a')
        (dayYoneda.{u} b) (dayYonedaMap.{u} α) x y) (ULift.up f, ULift.up g)
    simp only [comp_apply] at h
    rw [h]
    congr 1
  have hstep2 : (dayYoneda.{u} a' ◁ dayYonedaMap.{u} β).natTrans.app (x ⊗ y)
        ((DayFunctor.η (dayYoneda.{u} a') (dayYoneda.{u} b)).app (x, y)
          (ULift.up (f ≫ α), ULift.up g)) =
      (DayFunctor.η (dayYoneda.{u} a') (dayYoneda.{u} b')).app (x, y)
        (ULift.up (f ≫ α), ULift.up (g ≫ β)) := by
    have h := types_congr_hom
      (η_whiskerLeft_app (dayYoneda.{u} a') (dayYoneda.{u} b)
        (dayYoneda.{u} b') (dayYonedaMap.{u} β) x y)
      (ULift.up (f ≫ α), ULift.up g)
    simp only [comp_apply] at h
    rw [h]
    congr 1
  have hL : (dayTensorYonedaIso a' b').hom.natTrans.app (x ⊗ y)
        ((DayFunctor.η (dayYoneda.{u} a') (dayYoneda.{u} b')).app (x, y)
          (ULift.up (f ≫ α), ULift.up (g ≫ β))) =
      ULift.up ((f ≫ α) ⊗ₘ (g ≫ β)) := by
    have h := types_congr_hom
      (DayFunctor.η_comp_tensorDesc_app (yonedaTensorNatTrans.{u} a' b')
        x y) (ULift.up (f ≫ α), ULift.up (g ≫ β))
    simp only [comp_apply] at h
    change (DayFunctor.tensorDesc (yonedaTensorNatTrans.{u} a' b')).natTrans.app
        (x ⊗ y) _ = _
    rw [h]
    rfl
  have hR : (dayYonedaMap.{u} (α ⊗ₘ β)).natTrans.app (x ⊗ y)
        ((dayTensorYonedaIso a b).hom.natTrans.app (x ⊗ y)
          ((DayFunctor.η (dayYoneda.{u} a) (dayYoneda.{u} b)).app (x, y)
            (ULift.up f, ULift.up g))) =
      ULift.up ((f ⊗ₘ g) ≫ (α ⊗ₘ β)) := by
    have h := types_congr_hom
      (DayFunctor.η_comp_tensorDesc_app (yonedaTensorNatTrans.{u} a b)
        x y) (ULift.up f, ULift.up g)
    simp only [comp_apply] at h
    have hmid : (dayTensorYonedaIso a b).hom.natTrans.app (x ⊗ y)
          ((DayFunctor.η (dayYoneda.{u} a) (dayYoneda.{u} b)).app (x, y)
            (ULift.up f, ULift.up g)) = ULift.up (f ⊗ₘ g) := by
      change (DayFunctor.tensorDesc (yonedaTensorNatTrans.{u} a b)).natTrans.app
          (x ⊗ y) _ = _
      rw [h]
      rfl
    rw [hmid, dayYonedaMap_natTrans, hmap (α ⊗ₘ β) (x ⊗ y) (f ⊗ₘ g)]
  simp only [TypeCat.homEquiv_apply, comp_apply, htensor, dayCompNatTrans,
    NatTrans.comp_app]
  rw [hstep1, hstep2, hL, hR, MonoidalCategory.tensorHom_comp_tensorHom]

/-- The augmented hom obtained by tensoring `φ` with the
identity, read in `SimplexCategory`, is `tensorHomOf φ (𝟙 _)`:
the tensor of `of`-homs in the augmented simplex category is
definitionally `tensorHomOf`. -/
lemma down_ofHom_tensorHom_id {m m' : ℕ} (φ : ⦋m⦌ ⟶ ⦋m'⦌)
    (n : ℕ) :
    WithInitial.down (ofHom φ ⊗ₘ 𝟙 (WithInitial.of ⦋n⦌)) =
      AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌) :=
  rfl

/-- **Naturality of `augStdSimplexIso`** at the level of
augmented simplicial sets: the components are the identity away
from degree `-1`, where both sides land in a subsingleton. -/
lemma augStdSimplexIso_hom_naturality {m m' : ℕ} (φ : ⦋m⦌ ⟶ ⦋m'⦌) :
    Join.aug.map (stdSimplex.map φ) ≫ (Join.augStdSimplexIso ⦋m'⦌).hom =
      (Join.augStdSimplexIso ⦋m⦌).hom ≫ uliftYoneda.map (ofHom φ) := by
  apply NatTrans.ext
  funext x
  obtain ⟨a, rfl⟩ : ∃ a, x = op a := ⟨x.unop, rfl⟩
  cases a with
  | of k =>
      ext e
      obtain ⟨g⟩ := e
      rfl
  | star =>
      ext e
      apply ulift_hom_star_eq

/-- **Naturality of `augDayStdSimplexIso`** in `DayCat`. -/
lemma augDayStdSimplexIso_naturality {m m' : ℕ} (φ : ⦋m⦌ ⟶ ⦋m'⦌) :
    Join.augDay.map (stdSimplex.map φ) ≫
        (Join.augDayStdSimplexIso m').hom =
      (Join.augDayStdSimplexIso m).hom ≫ dayYonedaMap.{u} (ofHom φ) := by
  apply DayFunctor.hom_ext
  simp only [dayCompNatTrans, dayYonedaMap_natTrans]
  exact augStdSimplexIso_hom_naturality φ

/-- **Naturality of `dropYonedaIso`**: dropping the augmentation
of a representable map is the standard-simplex map of the
underlying simplex-category hom. -/
lemma dropYonedaIso_natural {a b : SimplexCategory}
    (γ : (WithInitial.of a : AugmentedSimplexCategory) ⟶ WithInitial.of b) :
    Join.dropDay.map (dayYonedaMap.{u} γ) ≫ (Join.dropYonedaIso b).hom =
      (Join.dropYonedaIso a).hom ≫ stdSimplex.map (WithInitial.down γ) := by
  apply NatTrans.ext
  funext x
  obtain ⟨k, rfl⟩ : ∃ k, x = op k := ⟨x.unop, rfl⟩
  ext e
  obtain ⟨g⟩ := e
  rfl

/-- The Day-level computation behind naturality of
`joinStdSimplexIso` in the left variable. -/
lemma augDay_map_whiskerRight_comp_joinStdSimplexIsoDay {m m' n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋m'⦌) :
    (Join.augDay.{u}.map (stdSimplex.map φ) ▷
        Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
        ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m')
            (Join.augDayStdSimplexIso.{u} n) ≪≫
          dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
            (WithInitial.of ⦋n⦌)).hom) =
      ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
          (Join.augDayStdSimplexIso.{u} n) ≪≫
        dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)).hom) ≫
        dayYonedaMap.{u}
          (ofHom φ ⊗ₘ 𝟙 (WithInitial.of ⦋n⦌)) := by
  calc (Join.augDay.{u}.map (stdSimplex.map φ) ▷
          Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
          ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m')
              (Join.augDayStdSimplexIso.{u} n) ≪≫
            dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
              (WithInitial.of ⦋n⦌)).hom)
      = ((Join.augDay.{u}.map (stdSimplex.map φ) ≫
            (Join.augDayStdSimplexIso.{u} m').hom) ⊗ₘ
          (Join.augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
            (WithInitial.of ⦋n⦌)).hom := by
        rw [← MonoidalCategory.tensorHom_id, Iso.trans_hom,
          MonoidalCategory.tensorIso_hom, ← Category.assoc,
          MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
    _ = (((Join.augDayStdSimplexIso.{u} m).hom ≫
            dayYonedaMap.{u} (ofHom φ)) ⊗ₘ
          (Join.augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
            (WithInitial.of ⦋n⦌)).hom := by
        rw [augDayStdSimplexIso_naturality]
    _ = ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (Join.augDayStdSimplexIso.{u} n).hom) ≫
          (dayYonedaMap.{u} (ofHom φ) ⊗ₘ
            𝟙 (dayYoneda.{u} (WithInitial.of ⦋n⦌))) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
            (WithInitial.of ⦋n⦌)).hom := by
        rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
          Category.comp_id]
    _ = ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (Join.augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom ≫
          dayYonedaMap.{u}
            (ofHom φ ⊗ₘ 𝟙 (WithInitial.of ⦋n⦌)) := by
        rw [← dayYonedaMap_id (WithInitial.of ⦋n⦌),
          dayTensorYonedaIso_natural]
    _ = ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
            (Join.augDayStdSimplexIso.{u} n) ≪≫
          dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom) ≫
          dayYonedaMap.{u}
            (ofHom φ ⊗ₘ 𝟙 (WithInitial.of ⦋n⦌)) := by
        rw [Iso.trans_hom, MonoidalCategory.tensorIso_hom, Category.assoc]

end Join

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `joinStdSimplexIso` in the left variable**:
joining a simplex-category map `φ` on the left and then applying
the join computation on standard simplices equals applying the
join computation first and then the ordinal-sum map
`tensorHomOf φ (𝟙 _)`. -/
theorem joinStdSimplexIso_natural_left {m m' n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋m'⦌) :
    (join.{u}.map (stdSimplex.map φ)).app (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m' n).hom =
      (joinStdSimplexIso.{u} m n).hom ≫
        stdSimplex.map (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌)) := by
  have hnat : Join.dropDay.{u}.map
        (Join.dayYonedaMap.{u} (Join.ofHom φ ⊗ₘ
            𝟙 (WithInitial.of ⦋n⦌))) ≫
        (Join.dropYonedaIso ⦋m' + n + 1⦌).hom =
      (Join.dropYonedaIso ⦋m + n + 1⦌).hom ≫
        stdSimplex.map (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌)) :=
    Join.dropYonedaIso_natural _
  have h1 : (joinStdSimplexIso.{u} m' n).hom =
      Join.dropDay.{u}.map
        ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m')
            (Join.augDayStdSimplexIso.{u} n) ≪≫
          Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
            (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m' + n + 1⦌).hom := rfl
  have h2 : (joinStdSimplexIso.{u} m n).hom =
      Join.dropDay.{u}.map
        ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
            (Join.augDayStdSimplexIso.{u} n) ≪≫
          Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := rfl
  have key : (join.{u}.map (stdSimplex.map φ)).app (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m' n).hom =
      (Join.dropDay.{u}.map
          ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
              (Join.augDayStdSimplexIso.{u} n) ≪≫
            Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        Join.dropDay.{u}.map
          (Join.dayYonedaMap.{u} (Join.ofHom φ ⊗ₘ
            𝟙 (WithInitial.of ⦋n⦌)))) ≫
        (Join.dropYonedaIso ⦋m' + n + 1⦌).hom := by
    have step1 : (join.{u}.map (stdSimplex.map φ)).app (Δ[n] : SSet.{u}) ≫
            (joinStdSimplexIso.{u} m' n).hom =
          (Join.dropDay.{u}.map
              (Join.augDay.{u}.map (stdSimplex.map φ) ▷
                Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            Join.dropDay.{u}.map
              ((MonoidalCategory.tensorIso
                  (Join.augDayStdSimplexIso.{u} m')
                  (Join.augDayStdSimplexIso.{u} n) ≪≫
                Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
                  (WithInitial.of ⦋n⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m' + n + 1⦌).hom := by
      rw [h1, join_map_app_eq]
      simp only [Category.assoc]
    have step2 : (Join.dropDay.{u}.map
              (Join.augDay.{u}.map (stdSimplex.map φ) ▷
                Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            Join.dropDay.{u}.map
              ((MonoidalCategory.tensorIso
                  (Join.augDayStdSimplexIso.{u} m')
                  (Join.augDayStdSimplexIso.{u} n) ≪≫
                Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
                  (WithInitial.of ⦋n⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m' + n + 1⦌).hom =
          Join.dropDay.{u}.map
              ((Join.augDay.{u}.map (stdSimplex.map φ) ▷
                  Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
                ((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m')
                    (Join.augDayStdSimplexIso.{u} n) ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
                    (WithInitial.of ⦋n⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m' + n + 1⦌).hom := by
      rw [← Join.dropDay.map_comp]
    have step3 : Join.dropDay.{u}.map
              ((Join.augDay.{u}.map (stdSimplex.map φ) ▷
                  Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
                ((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m')
                    (Join.augDayStdSimplexIso.{u} n) ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m'⦌)
                    (WithInitial.of ⦋n⦌)).hom)) ≫
            (Join.dropYonedaIso ⦋m' + n + 1⦌).hom =
          Join.dropDay.{u}.map
              (((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m)
                    (Join.augDayStdSimplexIso.{u} n) ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                    (WithInitial.of ⦋n⦌)).hom) ≫
                Join.dayYonedaMap.{u} (Join.ofHom φ ⊗ₘ
                  𝟙 (WithInitial.of ⦋n⦌))) ≫
            (Join.dropYonedaIso ⦋m' + n + 1⦌).hom := by
      rw [Join.augDay_map_whiskerRight_comp_joinStdSimplexIsoDay]
    have step4 : Join.dropDay.{u}.map
              (((MonoidalCategory.tensorIso
                    (Join.augDayStdSimplexIso.{u} m)
                    (Join.augDayStdSimplexIso.{u} n) ≪≫
                  Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                    (WithInitial.of ⦋n⦌)).hom) ≫
                Join.dayYonedaMap.{u} (Join.ofHom φ ⊗ₘ
                  𝟙 (WithInitial.of ⦋n⦌))) ≫
            (Join.dropYonedaIso ⦋m' + n + 1⦌).hom =
          (Join.dropDay.{u}.map
              ((MonoidalCategory.tensorIso
                  (Join.augDayStdSimplexIso.{u} m)
                  (Join.augDayStdSimplexIso.{u} n) ≪≫
                Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                  (WithInitial.of ⦋n⦌)).hom) ≫
            Join.dropDay.{u}.map
              (Join.dayYonedaMap.{u} (Join.ofHom φ ⊗ₘ
                𝟙 (WithInitial.of ⦋n⦌)))) ≫
            (Join.dropYonedaIso ⦋m' + n + 1⦌).hom := by
      rw [Join.dropDay.map_comp]
    exact step1.trans (step2.trans (step3.trans step4))
  have step5 : (Join.dropDay.{u}.map
            ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
                (Join.augDayStdSimplexIso.{u} n) ≪≫
              Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom) ≫
          Join.dropDay.{u}.map
            (Join.dayYonedaMap.{u} (Join.ofHom φ ⊗ₘ
              𝟙 (WithInitial.of ⦋n⦌)))) ≫
          (Join.dropYonedaIso ⦋m' + n + 1⦌).hom =
        Join.dropDay.{u}.map
            ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
                (Join.augDayStdSimplexIso.{u} n) ≪≫
              Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom) ≫
          (Join.dropYonedaIso ⦋m + n + 1⦌).hom ≫
            stdSimplex.map
              (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌)) := by
    simp only [Category.assoc]
    rw [hnat]
  have step6 : Join.dropDay.{u}.map
            ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
                (Join.augDayStdSimplexIso.{u} n) ≪≫
              Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom) ≫
          (Join.dropYonedaIso ⦋m + n + 1⦌).hom ≫
            stdSimplex.map
              (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌)) =
        (joinStdSimplexIso.{u} m n).hom ≫
          stdSimplex.map
            (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌)) := by
    conv_rhs => rw [h2]
    simp only [Category.assoc]
  exact key.trans (step5.trans step6)

/-!
### Simplex-category computations for joins

The simplex-category computations: `inl' ⦋n⦌ ⦋0⦌` is the last
face map, `inr' ⦋n⦌ ⦋0⦌` is the last-vertex inclusion, and
tensoring a face map with the identity on `⦋0⦌` is the same face
map one dimension up.
-/

/-- The face map of a standard simplex is `stdSimplex.map` of
the simplex-category face map, definitionally. -/
lemma stdSimplex_δ_eq_map {n : ℕ} (i : Fin (n + 2)) :
    (stdSimplex.δ i : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]) =
      stdSimplex.map (SimplexCategory.δ i) :=
  rfl

/-- `inl' ⦋n⦌ ⦋0⦌` is the last face map `δ_{n+1}`: both send
`i` to `i.castSucc`. -/
lemma inl'_eq_δ_last (n : ℕ) :
    AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ =
      SimplexCategory.δ (Fin.last (n + 1)) := by
  ext i : 3
  rw [AugmentedSimplexCategory.inl'_eval]
  have hδ : (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom i =
      i.castSucc := Fin.succAbove_last_apply i
  rw [hδ]
  rfl

/-- `inr' ⦋n⦌ ⦋0⦌` sends the unique vertex to the last vertex. -/
lemma inr'_toOrderHom_zero (n : ℕ) :
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom 0 =
      Fin.last (n + 1) := by
  apply Fin.ext
  rw [AugmentedSimplexCategory.inr'_eval]
  simp

/-- The last-vertex inclusion composed with a face map that does
not omit the last vertex is the last-vertex inclusion one
dimension up. -/
lemma inr'_comp_δ_castSucc {n : ℕ} (j : Fin (n + 2)) :
    AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ ≫
        SimplexCategory.δ j.castSucc =
      AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋0⦌ := by
  ext i : 3
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  rw [inr'_toOrderHom_zero, inr'_toOrderHom_zero]
  change Fin.succAbove j.castSucc (Fin.last (n + 1)) = Fin.last (n + 1 + 1)
  rw [Fin.succAbove_of_le_castSucc]
  · exact Fin.succ_last (n + 1)
  · simp only [Fin.castSucc_le_castSucc_iff]
    exact Fin.le_last j

/-- The simplicial identity needed below: the two ways of
skipping vertices `j` and `n + 2` agree. -/
lemma δ_last_comp_δ_castSucc {n : ℕ} (j : Fin (n + 2)) :
    SimplexCategory.δ (Fin.last (n + 1)) ≫ SimplexCategory.δ j.castSucc =
      SimplexCategory.δ j ≫ SimplexCategory.δ (Fin.last (n + 2)) := by
  have key := SimplexCategory.δ_comp_δ' (i := j) (j := Fin.last (n + 2))
    (Fin.castSucc_lt_last j)
  rw [Fin.pred_last] at key
  exact key.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a face map with the identity on `⦋0⦌` in the
augmented simplex category is the same face map one dimension
up. Proof by `tensorObj_hom_ext`: both `inl` and `inr`
precompositions agree, by `inl_comp_tensorHom`,
`inr_comp_tensorHom`, `SSet.inl'_eq_δ_last`,
`SSet.inr'_comp_δ_castSucc` and `SSet.δ_last_comp_δ_castSucc`
(the augmented equalities are the simplex-category equalities,
since homs between `of`-objects and their composition are
definitionally those of `SimplexCategory`). -/
lemma ofHom_δ_tensorHom_id {n : ℕ} (j : Fin (n + 2)) :
    Join.ofHom (SimplexCategory.δ j) ⊗ₘ 𝟙 (WithInitial.of ⦋0⦌) =
      Join.ofHom (SimplexCategory.δ j.castSucc) := by
  apply AugmentedSimplexCategory.tensorObj_hom_ext
  · rw [AugmentedSimplexCategory.inl_comp_tensorHom]
    change (SimplexCategory.δ j) ≫
        AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋0⦌ =
      AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ ≫
        SimplexCategory.δ j.castSucc
    rw [inl'_eq_δ_last, inl'_eq_δ_last]
    exact (δ_last_comp_δ_castSucc j).symm
  · rw [AugmentedSimplexCategory.inr_comp_tensorHom, Category.id_comp]
    change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋0⦌ =
      AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ ≫
        SimplexCategory.δ j.castSucc
    exact (inr'_comp_δ_castSucc j).symm

/-- `SSet.ofHom_δ_tensorHom_id` read in `SimplexCategory`:
`tensorHomOf (δ j) (𝟙 ⦋0⦌) = δ (castSucc j)`. -/
lemma tensorHomOf_δ_id {n : ℕ} (j : Fin (n + 2)) :
    AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ j)
        (𝟙 ⦋0⦌) =
      SimplexCategory.δ j.castSucc :=
  congrArg WithInitial.down (ofHom_δ_tensorHom_id j)

namespace Join

/-- Dropping the augmentation after `augDayStdSimplexIso` is the
identity on `Δ[m]`: both maps have identity components. -/
lemma dropDay_map_augDayStdSimplexIso_hom_comp_dropYonedaIso (m : ℕ) :
    dropDay.{u}.map (augDayStdSimplexIso.{u} m).hom ≫
        (dropYonedaIso ⦋m⦌).hom =
      𝟙 (Δ[m] : SSet.{u}) := by
  apply NatTrans.ext
  funext x
  obtain ⟨k, rfl⟩ : ∃ k, x = op k := ⟨x.unop, rfl⟩
  ext e
  obtain ⟨g⟩ := e
  rfl

/-- The right unitor at `op (of ⦋m⦌)` in the opposite augmented
simplex category is the identity: both augmented unitors are
`Iso.refl` on `of`-objects. -/
lemma rightUnitor_op_of_inv (m : ℕ) :
    (ρ_ (op (WithInitial.of ⦋m⦌) : AugmentedSimplexCategoryᵒᵖ)).inv =
      𝟙 (op (WithInitial.of ⦋m⦌)) :=
  rfl

/-- The unit element of `dayUnitYonedaIso`: it sends the Day
unit element `ν` to the identity of `star`. -/
lemma dayUnitYonedaIso_hom_app_ν :
    dayUnitYonedaIso.{u}.hom.natTrans.app (op WithInitial.star)
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit) =
      ULift.up (𝟙 WithInitial.star) := by
  have h := types_congr_hom
    (DayFunctor.ν_comp_unitDesc
      (F := dayYoneda.{u} WithInitial.star)
      (↾fun _ ↦ ULift.up (𝟙 WithInitial.star))) PUnit.unit
  simp only [comp_apply] at h
  exact h

/-- `augDayBotIso.inv` sends the identity of `star` to the
unique point. -/
lemma augDayBotIso_inv_app_star :
    augDayBotIso.{u}.inv.natTrans.app (op WithInitial.star)
        (ULift.up (𝟙 WithInitial.star)) = PUnit.unit :=
  rfl

/-- Any element of an augmented extension in degree `-1` is the
unique point; applied to maps out of the empty simplicial set. -/
lemma augDay_map_initial_to_app_star {Y : SSet.{u}} :
    (augDay.{u}.map (initial.to Y)).natTrans.app (op WithInitial.star)
        PUnit.unit = PUnit.unit :=
  @Subsingleton.elim (PUnit : Type u) _ _ _

/-- The `augDayStdSimplexIso` components on the two elements
that occur in the chase: the identity at `of ⦋m⦌`, and the
unique map out of `star` in degree `-1`. -/
lemma augDayStdSimplexIso_hom_app_of (m : ℕ) :
    (augDayStdSimplexIso.{u} m).hom.natTrans.app
        (op (WithInitial.of ⦋m⦌)) (ULift.up (𝟙 ⦋m⦌)) =
      ULift.up (𝟙 (WithInitial.of ⦋m⦌)) :=
  rfl

lemma augDayStdSimplexIso_hom_app_star (n : ℕ) :
    (augDayStdSimplexIso.{u} n).hom.natTrans.app (op WithInitial.star)
        PUnit.unit =
      ULift.up (WithInitial.starInitial.to (WithInitial.of ⦋n⦌)) :=
  rfl

lemma augDayStdSimplexIso_inv_app_of (m : ℕ) :
    (augDayStdSimplexIso.{u} m).inv.natTrans.app
        (op (WithInitial.of ⦋m⦌)) (ULift.up (𝟙 (WithInitial.of ⦋m⦌))) =
      ULift.up (𝟙 ⦋m⦌) :=
  rfl

/-- In the augmented simplex category, `inl` at `of`-objects is
tensoring with the identity on the left: the right unitor there
is `Iso.refl`. -/
lemma inl_of_eq (m n : ℕ) :
    AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
        (WithInitial.of ⦋n⦌) =
      𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
        WithInitial.starInitial.to (WithInitial.of ⦋n⦌) := by
  have hρ : (ρ_ (WithInitial.of ⦋m⦌)) = Iso.refl (WithInitial.of ⦋m⦌) :=
    rfl
  rw [AugmentedSimplexCategory.inl, hρ]
  simp only [Iso.refl_inv, MonoidalCategory.id_tensorHom]
  exact Category.id_comp _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The right-unitor element computation**: the inverse right
unitor in `DayCat` sends an element `e` at `op (of ⦋m⦌)` to
the `η`-element `(e, ν)`. This is
`LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app`
evaluated at `(e, ⋆)`, using that the unitor at
`op (of ⦋m⦌)` is the identity (`Join.rightUnitor_op_of_inv`)
and that the type-level right unitor is the first projection. -/
lemma rightUnitor_inv_app_of (m : ℕ) :
    (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv.natTrans.app
        (op (WithInitial.of ⦋m⦌)) (ULift.up (𝟙 ⦋m⦌)) =
      (DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u})) (𝟙_ DayCat.{u})).app
        (op (WithInitial.of ⦋m⦌), op WithInitial.star)
        (ULift.up (𝟙 ⦋m⦌),
          DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit) := by
  have hstruct :=
    LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app
      (Type u) (augDay.{u}.obj (Δ[m] : SSet.{u}))
      (op (WithInitial.of ⦋m⦌))
  have hstruct' : ((augDay.{u}.obj (Δ[m] : SSet.{u})).functor.obj
          (op (WithInitial.of ⦋m⦌)) ◁
        DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)) ≫
        (DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
          (𝟙_ DayCat.{u})).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star) ≫
        (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).hom.natTrans.app
          (op (WithInitial.of ⦋m⦌)) =
      (ρ_ ((augDay.{u}.obj (Δ[m] : SSet.{u})).functor.obj
          (op (WithInitial.of ⦋m⦌)))).hom ≫
        (augDay.{u}.obj (Δ[m] : SSet.{u})).functor.map
          (ρ_ (op (WithInitial.of ⦋m⦌))).inv :=
    hstruct
  have h2 := types_congr_hom hstruct'
    (ULift.up (𝟙 ⦋m⦌), (PUnit.unit : (PUnit : Type u)))
  simp only [comp_apply] at h2
  have h2' : (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).hom.natTrans.app
        (op (WithInitial.of ⦋m⦌))
        ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
            (𝟙_ DayCat.{u})).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (ULift.up (𝟙 ⦋m⦌),
            DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
              PUnit.unit)) =
      ULift.up (𝟙 ⦋m⦌) := by
    have hmapid : (augDay.{u}.obj (Δ[m] : SSet.{u})).functor.map
          (ρ_ (op (WithInitial.of ⦋m⦌))).inv (ULift.up (𝟙 ⦋m⦌)) =
        ULift.up (𝟙 ⦋m⦌) := by
      rw [rightUnitor_op_of_inv]
      simp only [CategoryTheory.Functor.map_id]
      rfl
    exact h2.trans hmapid
  have hcomp : (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv.natTrans.app
        (op (WithInitial.of ⦋m⦌))
        ((ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).hom.natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
              (𝟙_ DayCat.{u})).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 ⦋m⦌),
              DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
                PUnit.unit))) =
      (DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
          (𝟙_ DayCat.{u})).app
        (op (WithInitial.of ⦋m⦌), op WithInitial.star)
        (ULift.up (𝟙 ⦋m⦌),
          DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
            PUnit.unit) := by
    have hid : ((ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).hom ≫
          (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv).natTrans =
        𝟙 _ := by
      have hcong := congrArg DayFunctor.Hom.natTrans
        (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).hom_inv_id
      rwa [dayIdNatTrans] at hcong
    have happ := types_congr_hom
      (NatTrans.congr_app hid (op (WithInitial.of ⦋m⦌)))
      ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
          (𝟙_ DayCat.{u})).app
        (op (WithInitial.of ⦋m⦌), op WithInitial.star)
        (ULift.up (𝟙 ⦋m⦌),
          DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit))
    simp only [NatTrans.id_app,
      types_id_apply] at happ
    exact happ
  rw [h2'] at hcomp
  exact hcomp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The Yoneda-element chase for `joinInl`**: the composite in
`DayCat` obtained by expanding `joinInl Δ[m] Δ[n]` (right unitor,
then whiskering the unique map out of the empty simplicial set)
and `joinStdSimplexIso m n` equals `augDayStdSimplexIso` followed
by the representable map of `inl`. The proof evaluates both
sides, after precomposing with `(augDayStdSimplexIso m).inv`,
on the universal element `ULift.up (𝟙 (of ⦋m⦌))`:
`Join.rightUnitor_inv_app_of` writes it as an `η`-element, the
whisker steps (`η_whiskerLeft_app`, `η_whiskerRight_app` of
`JoinProperties.lean`) push it through the tensor, the degree
`-1` components compute by the `rfl` lemmas above, and
`η_comp_tensorDesc_app` finishes at
`ULift.up (𝟙 ⊗ₘ starInitial.to) = ULift.up (inl ..)`
(`Join.inl_of_eq`). -/
lemma joinInlDay_eq (m n : ℕ) :
    (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
        (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁ dayUnitYonedaIso.{u}.hom) ≫
        (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁ augDayBotIso.{u}.inv) ≫
        (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
          augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
        ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (augDayStdSimplexIso.{u} n).hom) ≫
        (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)).hom =
      (augDayStdSimplexIso.{u} m).hom ≫
        dayYonedaMap.{u}
          (AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)) := by
  have key : (augDayStdSimplexIso.{u} m).inv ≫
        ((ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
          (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁ dayUnitYonedaIso.{u}.hom) ≫
          (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁ augDayBotIso.{u}.inv) ≫
          (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
            augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
          ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
            (augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom) =
      dayYonedaMap.{u}
        (AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)) := by
    have s3 : (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
          dayUnitYonedaIso.{u}.hom).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
              (𝟙_ DayCat.{u})).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 ⦋m⦌),
              DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u)
                PUnit.unit)) =
        (DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
            (dayYoneda.{u} WithInitial.star)).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (ULift.up (𝟙 ⦋m⦌), ULift.up (𝟙 WithInitial.star)) := by
      have h := types_congr_hom
        (η_whiskerLeft_app (augDay.{u}.obj (Δ[m] : SSet.{u}))
          (𝟙_ DayCat.{u}) (dayYoneda.{u} WithInitial.star)
          dayUnitYonedaIso.{u}.hom (op (WithInitial.of ⦋m⦌))
          (op WithInitial.star))
        (ULift.up (𝟙 ⦋m⦌),
          DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit)
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s4 : (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
          augDayBotIso.{u}.inv).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
              (dayYoneda.{u} WithInitial.star)).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 ⦋m⦌), ULift.up (𝟙 WithInitial.star))) =
        (DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
            (augDay.{u}.obj (⊥_ SSet.{u}))).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (ULift.up (𝟙 ⦋m⦌), PUnit.unit) := by
      have h := types_congr_hom
        (η_whiskerLeft_app (augDay.{u}.obj (Δ[m] : SSet.{u}))
          (dayYoneda.{u} WithInitial.star)
          (augDay.{u}.obj (⊥_ SSet.{u}))
          augDayBotIso.{u}.inv (op (WithInitial.of ⦋m⦌))
          (op WithInitial.star))
        (ULift.up (𝟙 ⦋m⦌), ULift.up (𝟙 WithInitial.star))
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s5 : (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
          augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
              (augDay.{u}.obj (⊥_ SSet.{u}))).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 ⦋m⦌), PUnit.unit)) =
        (DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
            (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (ULift.up (𝟙 ⦋m⦌), PUnit.unit) := by
      have h := types_congr_hom
        (η_whiskerLeft_app (augDay.{u}.obj (Δ[m] : SSet.{u}))
          (augDay.{u}.obj (⊥_ SSet.{u}))
          (augDay.{u}.obj (Δ[n] : SSet.{u}))
          (augDay.{u}.map (initial.to (Δ[n] : SSet.{u})))
          (op (WithInitial.of ⦋m⦌)) (op WithInitial.star))
        (ULift.up (𝟙 ⦋m⦌), PUnit.unit)
      simp only [comp_apply] at h
      refine h.trans ?_
      congr 1
    have s6 : ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (augDayStdSimplexIso.{u} n).hom).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 ⦋m⦌), PUnit.unit)) =
        (DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
            (dayYoneda.{u} (WithInitial.of ⦋n⦌))).app
          (op (WithInitial.of ⦋m⦌), op WithInitial.star)
          (ULift.up (𝟙 (WithInitial.of ⦋m⦌)),
            ULift.up
              (WithInitial.starInitial.to (WithInitial.of ⦋n⦌))) := by
      have ht : ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
            (augDayStdSimplexIso.{u} n).hom) =
          ((augDayStdSimplexIso.{u} m).hom ▷
              augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
            (dayYoneda.{u} (WithInitial.of ⦋m⦌) ◁
              (augDayStdSimplexIso.{u} n).hom) :=
        MonoidalCategory.tensorHom_def _ _
      have hs1 : ((augDayStdSimplexIso.{u} m).hom ▷
            augDay.{u}.obj (Δ[n] : SSet.{u})).natTrans.app
            (op (WithInitial.of ⦋m⦌))
            ((DayFunctor.η (augDay.{u}.obj (Δ[m] : SSet.{u}))
                (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
              (op (WithInitial.of ⦋m⦌), op WithInitial.star)
              (ULift.up (𝟙 ⦋m⦌), PUnit.unit)) =
          (DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
              (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 (WithInitial.of ⦋m⦌)), PUnit.unit) := by
        have h := types_congr_hom
          (η_whiskerRight_app (augDay.{u}.obj (Δ[m] : SSet.{u}))
            (dayYoneda.{u} (WithInitial.of ⦋m⦌))
            (augDay.{u}.obj (Δ[n] : SSet.{u}))
            (augDayStdSimplexIso.{u} m).hom
            (op (WithInitial.of ⦋m⦌)) (op WithInitial.star))
          (ULift.up (𝟙 ⦋m⦌), PUnit.unit)
        simp only [comp_apply] at h
        refine h.trans ?_
        congr 1
      have hs2 : (dayYoneda.{u} (WithInitial.of ⦋m⦌) ◁
            (augDayStdSimplexIso.{u} n).hom).natTrans.app
            (op (WithInitial.of ⦋m⦌))
            ((DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
                (augDay.{u}.obj (Δ[n] : SSet.{u}))).app
              (op (WithInitial.of ⦋m⦌), op WithInitial.star)
              (ULift.up (𝟙 (WithInitial.of ⦋m⦌)), PUnit.unit)) =
          (DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
              (dayYoneda.{u} (WithInitial.of ⦋n⦌))).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 (WithInitial.of ⦋m⦌)),
              ULift.up
                (WithInitial.starInitial.to
                  (WithInitial.of ⦋n⦌))) := by
        have h := types_congr_hom
          (η_whiskerLeft_app (dayYoneda.{u} (WithInitial.of ⦋m⦌))
            (augDay.{u}.obj (Δ[n] : SSet.{u}))
            (dayYoneda.{u} (WithInitial.of ⦋n⦌))
            (augDayStdSimplexIso.{u} n).hom
            (op (WithInitial.of ⦋m⦌)) (op WithInitial.star))
          (ULift.up (𝟙 (WithInitial.of ⦋m⦌)), PUnit.unit)
        simp only [comp_apply] at h
        refine h.trans ?_
        congr 1
      rw [ht]
      simp only [dayCompNatTrans, NatTrans.comp_app, comp_apply]
      rw [hs1, hs2]
    have s7 : (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)).hom.natTrans.app
          (op (WithInitial.of ⦋m⦌))
          ((DayFunctor.η (dayYoneda.{u} (WithInitial.of ⦋m⦌))
              (dayYoneda.{u} (WithInitial.of ⦋n⦌))).app
            (op (WithInitial.of ⦋m⦌), op WithInitial.star)
            (ULift.up (𝟙 (WithInitial.of ⦋m⦌)),
              ULift.up
                (WithInitial.starInitial.to
                  (WithInitial.of ⦋n⦌)))) =
        ULift.up (𝟙 (WithInitial.of ⦋m⦌) ⊗ₘ
          WithInitial.starInitial.to (WithInitial.of ⦋n⦌)) := by
      have h := types_congr_hom
        (DayFunctor.η_comp_tensorDesc_app
          (yonedaTensorNatTrans.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌))
          (op (WithInitial.of ⦋m⦌)) (op WithInitial.star))
        (ULift.up (𝟙 (WithInitial.of ⦋m⦌)),
          ULift.up
            (WithInitial.starInitial.to (WithInitial.of ⦋n⦌)))
      simp only [comp_apply] at h
      exact h
    apply DayFunctor.hom_ext
    apply uliftYonedaEquiv.injective
    rw [show uliftYonedaEquiv
          ((augDayStdSimplexIso.{u} m).inv ≫
            ((ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
              (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                dayUnitYonedaIso.{u}.hom) ≫
              (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                augDayBotIso.{u}.inv) ≫
              (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
              ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
                (augDayStdSimplexIso.{u} n).hom) ≫
              (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom)).natTrans =
        ((augDayStdSimplexIso.{u} m).inv ≫
          ((ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
            (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              dayUnitYonedaIso.{u}.hom) ≫
            (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              augDayBotIso.{u}.inv) ≫
            (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
            ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (augDayStdSimplexIso.{u} n).hom) ≫
            (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom)).natTrans.app
          (op (WithInitial.of ⦋m⦌))
          (ULift.up (𝟙 (WithInitial.of ⦋m⦌))) from rfl,
      show uliftYonedaEquiv
          (dayYonedaMap.{u}
            (AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌))).natTrans =
        ULift.up (𝟙 (WithInitial.of ⦋m⦌) ≫
          AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)) from rfl]
    simp only [dayCompNatTrans, NatTrans.comp_app, comp_apply]
    rw [augDayStdSimplexIso_inv_app_of, rightUnitor_inv_app_of, s3, s4,
      s5, s6, s7, Category.id_comp, inl_of_eq]
  calc (ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
          (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁ dayUnitYonedaIso.{u}.hom) ≫
          (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁ augDayBotIso.{u}.inv) ≫
          (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
            augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
          ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
            (augDayStdSimplexIso.{u} n).hom) ≫
          (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)).hom
      = (augDayStdSimplexIso.{u} m).hom ≫
          ((augDayStdSimplexIso.{u} m).inv ≫
            ((ρ_ (augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
              (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                dayUnitYonedaIso.{u}.hom) ≫
              (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                augDayBotIso.{u}.inv) ≫
              (augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
                augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
              ((augDayStdSimplexIso.{u} m).hom ⊗ₘ
                (augDayStdSimplexIso.{u} n).hom) ≫
              (dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌)).hom)) := by
        conv_rhs => rw [← Category.assoc,
          (augDayStdSimplexIso.{u} m).hom_inv_id, Category.id_comp]
    _ = (augDayStdSimplexIso.{u} m).hom ≫
          dayYonedaMap.{u}
            (AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)) := by
        rw [key]

end Join

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **`joinInl` on standard simplices is `inl'`**: the left
endpoint inclusion of a join of standard simplices, transported
along `joinStdSimplexIso`, is the standard-simplex map of
`AugmentedSimplexCategory.inl'`. Expanding `joinInl`
(right unitor, then
whiskering `initial.to`) and `joinStdSimplexIso` in `DayCat`
reduces it to `Join.joinInlDay_eq` and naturality of
`dropYonedaIso`. -/
theorem joinInl_comp_joinStdSimplexIso_hom (m n : ℕ) :
    joinInl (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m n).hom =
      stdSimplex.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋n⦌) := by
  have hInl : joinInl (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) =
      Join.dropDay.{u}.map
        ((ρ_ (Join.augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
          (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
            Join.dayUnitYonedaIso.{u}.hom) ≫
          (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
            Join.augDayBotIso.{u}.inv) ≫
          (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
            Join.augDay.{u}.map (initial.to (Δ[n] : SSet.{u})))) := by
    simp only [joinInl, joinBotIso, join_obj_map_eq, Functor.mapIso_inv,
      Iso.trans_inv, MonoidalCategory.tensorIso_inv, Iso.refl_inv,
      Iso.symm_inv, MonoidalCategory.id_tensorHom,
      ← Join.dropDay.map_comp, Category.assoc]
  have hIso : (joinStdSimplexIso.{u} m n).hom =
      Join.dropDay.{u}.map
          (((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (Join.augDayStdSimplexIso.{u} n).hom) ≫
            (Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := by
    have hrfl : (joinStdSimplexIso.{u} m n).hom =
        Join.dropDay.{u}.map
          ((MonoidalCategory.tensorIso (Join.augDayStdSimplexIso.{u} m)
              (Join.augDayStdSimplexIso.{u} n) ≪≫
            Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
          (Join.dropYonedaIso ⦋m + n + 1⦌).hom := rfl
    rw [hrfl, Iso.trans_hom, MonoidalCategory.tensorIso_hom]
  have step1 : joinInl (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m n).hom =
      Join.dropDay.{u}.map
          ((ρ_ (Join.augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
            (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              Join.dayUnitYonedaIso.{u}.hom) ≫
            (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              Join.augDayBotIso.{u}.inv) ≫
            (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              Join.augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
            ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (Join.augDayStdSimplexIso.{u} n).hom) ≫
            (Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := by
    rw [hInl, hIso]
    simp only [← Category.assoc, ← Join.dropDay.map_comp]
  have step2 : Join.dropDay.{u}.map
          ((ρ_ (Join.augDay.{u}.obj (Δ[m] : SSet.{u}))).inv ≫
            (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              Join.dayUnitYonedaIso.{u}.hom) ≫
            (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              Join.augDayBotIso.{u}.inv) ≫
            (Join.augDay.{u}.obj (Δ[m] : SSet.{u}) ◁
              Join.augDay.{u}.map (initial.to (Δ[n] : SSet.{u}))) ≫
            ((Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
              (Join.augDayStdSimplexIso.{u} n).hom) ≫
            (Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
              (WithInitial.of ⦋n⦌)).hom) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom =
      Join.dropDay.{u}.map
          ((Join.augDayStdSimplexIso.{u} m).hom ≫
            Join.dayYonedaMap.{u}
              (AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌))) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom := by
    rw [Join.joinInlDay_eq]
  have step3 : Join.dropDay.{u}.map
          ((Join.augDayStdSimplexIso.{u} m).hom ≫
            Join.dayYonedaMap.{u}
              (AugmentedSimplexCategory.inl (WithInitial.of ⦋m⦌)
                (WithInitial.of ⦋n⦌))) ≫
        (Join.dropYonedaIso ⦋m + n + 1⦌).hom =
      stdSimplex.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋n⦌) := by
    rw [Join.dropDay.map_comp]
    simp only [Category.assoc]
    rw [Join.dropYonedaIso_natural,
      ← Category.assoc (Join.dropDay.{u}.map
        (Join.augDayStdSimplexIso.{u} m).hom),
      Join.dropDay_map_augDayStdSimplexIso_hom_comp_dropYonedaIso]
    exact Category.id_comp _
  exact step1.trans (step2.trans step3)

/-- The conjugation form of naturality of `joinStdSimplexIso`:
precomposition with its inverse commutes with joins of
simplex-category maps. -/
theorem joinStdSimplexIso_inv_comp_join_map_app {m m' : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋m'⦌) (n : ℕ) :
    (joinStdSimplexIso.{u} m n).inv ≫
        (join.{u}.map (stdSimplex.map φ)).app (Δ[n] : SSet.{u}) =
      stdSimplex.map (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌)) ≫
        (joinStdSimplexIso.{u} m' n).inv := by
  have h := joinStdSimplexIso_natural_left φ (n := n)
  rw [Iso.inv_comp_eq, ← Category.assoc (joinStdSimplexIso.{u} m n).hom,
    ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SSet

end
