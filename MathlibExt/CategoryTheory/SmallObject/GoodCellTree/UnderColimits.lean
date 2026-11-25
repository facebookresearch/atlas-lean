/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Original root-adjoined colimits and free under-root pushouts

The native WithInitial construction retains every original star and vertex
map. The original costar/forget hom equivalence transposes a given raw cell
pushout, including its entire descender and uniqueness. Roots are arbitrary.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t v u vJ uJ

namespace CategoryTheory.SmallObject.UnderColimits

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section RootAdjoined

variable {X : C} {J : Type uJ} [Category.{vJ} J] {Y : J ⥤ Under X}

/-- The original native diagram with the same root adjoined as its star. -/
abbrev adjoinedDiagram : WithInitial J ⥤ C :=
  WithInitial.liftFromUnder.obj Y

/-- The native root-adjoined cocone keeps the original underlying point and maps. -/
abbrev adjoinedCocone (c : Cocone Y) : Cocone (adjoinedDiagram (Y := Y)) :=
  WithInitial.coconeEquiv.functor.obj c

/-- The original Under colimit is a colimit of its same native adjoined diagram. -/
abbrev adjoinedColimit (c : ColimitCocone Y) :
    ColimitCocone (adjoinedDiagram (Y := Y)) where
  cocone := adjoinedCocone c.cocone
  isColimit := (WithInitial.isColimitEquiv (t := c.cocone)).symm c.isColimit

@[simp]
theorem adjoined_point (c : Cocone Y) : (adjoinedCocone c).pt = c.pt.right := rfl

@[reassoc]
theorem adjoined_star (c : Cocone Y) :
    (adjoinedCocone c).ι.app WithInitial.star = c.pt.hom :=
  WithInitial.coconeEquiv_functor_obj_ι_app_star

@[reassoc]
theorem adjoined_vertex (c : Cocone Y) (j : J) :
    (adjoinedCocone c).ι.app (WithInitial.of j) = (c.ι.app j).right :=
  WithInitial.coconeEquiv_functor_obj_ι_app_of j

end RootAdjoined

/-- The same forgetful functor preserves every cardinal-filtered colimit at this cardinal. -/
instance forgetIsCardinalAccessible (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (Under.forget X).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    let : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
    let : IsConnected J := IsFiltered.isConnected J
    infer_instance

section Costar

variable [HasBinaryCoproducts C] {X : C}

/-- The original native costar/forget transposition, with its exact chosen adjunction. -/
abbrev transpose {A : C} {U : Under X} (a : A ⟶ U.right) :
    (Under.costar X).obj A ⟶ U :=
  ((Under.costarAdjForget X).homEquiv A U).symm a

/-- The whole original transposition and evaluation functions are mutual inverses. -/
theorem transpose_homEquiv_function :
    (fun (A : C) (U : Under X) (a : A ⟶ U.right) =>
      (Under.costarAdjForget X).homEquiv A U (transpose a)) =
    (fun (A : C) (U : Under X) (a : A ⟶ U.right) => a) := by
  funext A U a
  exact ((Under.costarAdjForget X).homEquiv A U).apply_symm_apply a

/-- The source-variable equation retains the original costar map and original arrow. -/
theorem transpose_source {A B : C} {U : Under X} (s : A ⟶ B) (b : B ⟶ U.right) :
    (Under.costar X).map s ≫ transpose b = transpose (s ≫ b) :=
  ((Under.costarAdjForget X).homEquiv_naturality_left_symm s b).symm

/-- The target-variable equation retains the original under morphism and raw component. -/
theorem transpose_target {A : C} {U V : Under X} (a : A ⟶ U.right) (p : U ⟶ V) :
    transpose a ≫ p = transpose (a ≫ p.right) :=
  ((Under.costarAdjForget X).homEquiv_naturality_right_symm a p).symm

/-- The same free object is presentable relative to any original root. -/
theorem costarPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (A : C) [IsCardinalPresentable A κ] :
    IsCardinalPresentable ((Under.costar X).obj A) κ :=
  (Under.costarAdjForget X).isCardinalPresentable_leftAdjoint_obj κ A

section Pushout

variable {A B : C} {U V : Under X}
  {s : A ⟶ B} {a : A ⟶ U.right} {b : B ⟶ V.right} {p : U ⟶ V}
  (hs : IsPushout a s p.right b)

include hs in
/-- The entire original raw square transposes to the actual free under-root square. -/
theorem freeSquare :
    transpose a ≫ p = (Under.costar X).map s ≫ transpose b := by
  rw [transpose_target, transpose_source]
  exact congrArg (fun k => transpose (U := V) k) hs.w

/-- A given free-under cocone has the original raw cell compatibility equation. -/
theorem rawCondition (c : PushoutCocone (transpose a) ((Under.costar X).map s)) :
    a ≫ c.inl.right = s ≫ (Under.costarAdjForget X).homEquiv B c.pt c.inr := by
  have h := congrArg ((Under.costarAdjForget X).homEquiv A c.pt) c.condition
  rw [(Under.costarAdjForget X).homEquiv_naturality_right,
    (Under.costarAdjForget X).homEquiv_naturality_left] at h
  simpa only [transpose, Equiv.apply_symm_apply, Under.forget_obj, Under.forget_map] using h

/-- The original raw pushout descender for precisely this given under cocone. -/
abbrev rawDesc (c : PushoutCocone (transpose a) ((Under.costar X).map s)) :
    V.right ⟶ c.pt.right :=
  hs.desc c.inl.right ((Under.costarAdjForget X).homEquiv B c.pt c.inr) (rawCondition c)

/-- Its original source-root equation follows from the given predecessor root and leg. -/
theorem rawDesc_root (c : PushoutCocone (transpose a) ((Under.costar X).map s)) :
    V.hom ≫ rawDesc hs c = c.pt.hom := by
  rw [← Under.w p, Category.assoc, hs.inl_desc]
  exact Under.w c.inl

/-- The full original raw descender, promoted under the same arbitrary root. -/
abbrev desc (c : PushoutCocone (transpose a) ((Under.costar X).map s)) :
    V ⟶ c.pt :=
  Under.homMk (rawDesc hs c) (rawDesc_root hs c)

@[reassoc]
theorem desc_left (c : PushoutCocone (transpose a) ((Under.costar X).map s)) :
    p ≫ desc hs c = c.inl := by
  apply Under.UnderMorphism.ext
  exact hs.inl_desc c.inl.right ((Under.costarAdjForget X).homEquiv B c.pt c.inr)
    (rawCondition c)

@[reassoc]
theorem desc_right (c : PushoutCocone (transpose a) ((Under.costar X).map s)) :
    transpose b ≫ desc hs c = c.inr := by
  apply ((Under.costarAdjForget X).homEquiv B c.pt).injective
  rw [(Under.costarAdjForget X).homEquiv_naturality_right]
  simp only [transpose, Equiv.apply_symm_apply]
  exact hs.inr_desc c.inl.right ((Under.costarAdjForget X).homEquiv B c.pt c.inr)
    (rawCondition c)

/-- Both original under-root legs detect the complete original descender function. -/
theorem desc_uniq (c : PushoutCocone (transpose a) ((Under.costar X).map s))
    (m : V ⟶ c.pt) (hLeft : p ≫ m = c.inl) (hRight : transpose b ≫ m = c.inr) :
    m = desc hs c := by
  apply Under.UnderMorphism.ext
  apply hs.hom_ext
  · exact (congrArg Under.Hom.right hLeft).trans
      (hs.inl_desc c.inl.right ((Under.costarAdjForget X).homEquiv B c.pt c.inr)
        (rawCondition c)).symm
  · have hb := congrArg ((Under.costarAdjForget X).homEquiv B c.pt) hRight
    rw [(Under.costarAdjForget X).homEquiv_naturality_right] at hb
    simp only [transpose, Equiv.apply_symm_apply] at hb
    exact hb.trans
      (hs.inr_desc c.inl.right ((Under.costarAdjForget X).homEquiv B c.pt c.inr)
        (rawCondition c)).symm

include hs in
/-- The given raw pushout supplies the genuine entire free-under universal property. -/
theorem isPushout :
    IsPushout (transpose a) ((Under.costar X).map s) p (transpose b) := by
  refine ⟨⟨freeSquare hs⟩,
    ⟨PushoutCocone.IsColimit.mk (freeSquare hs) ?_ ?_ ?_ ?_⟩⟩
  · intro c
    exact desc hs c
  · intro c
    exact desc_left hs c
  · intro c
    exact desc_right hs c
  · intro c m hLeft hRight
    exact desc_uniq hs c m hLeft hRight

end Pushout

/-- Every original cell occurrence has its genuine free-under pushout with the same maps. -/
theorem treeFreePushout {P : Type w} [PartialOrder P] {α : Type t}
    {s : α → Arrow C} (T : CellTree s X (P := P)) (a : P) :
    IsPushout (transpose (T.attaching a)) ((Under.costar X).map (s (T.label a)).hom)
      (T.predecessorMap a) (transpose (T.cell a)) :=
  isPushout (T.isPushout a)

end Costar

end CategoryTheory.SmallObject.UnderColimits
