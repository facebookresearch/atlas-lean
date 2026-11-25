/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Transport of functor comparisons through source refinements

Associators and whiskering assemble a comparison after a source functor.
The source refinement and intermediate comparison are natural
isomorphisms. Component and natural-transformation laws preserve their
maps, without resolution or smallness hypotheses on the input category.
-/

@[expose] public section

open CategoryTheory

universe uB vB uC vC uD vD uE vE uE' vE'

namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {E' : Type uE'} [Category.{vE'} E']
  (W : B ⥤ C) (W' : B ⥤ D) (U : C ⥤ D) (V : E ⥤ E')
  (F : C ⥤ E) (G : D ⥤ E')
  (a : F ⋙ V ≅ U ⋙ G) (s : W ⋙ U ≅ W')

/-- Compare the actual source-precomposed functors using native association and refinement. -/
def precompositionComparisonIso : (W ⋙ F) ⋙ V ≅ W' ⋙ G :=
  Functor.associator W F V ≪≫ isoWhiskerLeft W a ≪≫
    (Functor.associator W U G).symm ≪≫ isoWhiskerRight s G

/-- The hom first applies the original comparison, then the actual source refinement. -/
theorem precompositionComparisonIso_hom_app (X : B) :
    (precompositionComparisonIso W W' U V F G a s).hom.app X =
      a.hom.app (W.obj X) ≫ G.map (s.hom.app X) := by
  change (𝟙 _) ≫ a.hom.app (W.obj X) ≫ (𝟙 _) ≫ G.map (s.hom.app X) = _
  simp only [Category.id_comp, Category.comp_id]

/-- The inverse inserts the actual source refinement inverse before the comparison inverse. -/
theorem precompositionComparisonIso_inv_app (X : B) :
    (precompositionComparisonIso W W' U V F G a s).inv.app X =
      G.map (s.inv.app X) ≫ a.inv.app (W.obj X) := by
  change ((G.map (s.inv.app X) ≫ (𝟙 _)) ≫ a.inv.app (W.obj X)) ≫ (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Actual intermediate natural-transformation squares survive source refinement. -/
theorem precompositionComparisonIso_naturality
    {F' : C ⥤ E} {G' : D ⥤ E'} (α : F ⟶ F') (β : G ⟶ G')
    (a' : F' ⋙ V ≅ U ⋙ G')
    (h : whiskerRight α V ≫ a'.hom = a.hom ≫ whiskerLeft U β) :
    whiskerRight (whiskerLeft W α) V ≫
        (precompositionComparisonIso W W' U V F' G' a' s).hom =
      (precompositionComparisonIso W W' U V F G a s).hom ≫ whiskerLeft W' β := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [precompositionComparisonIso_hom_app, precompositionComparisonIso_hom_app]
  have hCore : V.map (α.app (W.obj X)) ≫ a'.hom.app (W.obj X) =
      a.hom.app (W.obj X) ≫ β.app (U.obj (W.obj X)) := by
    have h' := congrArg (fun γ => γ.app (W.obj X)) h
    simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] using h'
  have hRefinement : G.map (s.hom.app X) ≫ β.app (W'.obj X) =
      β.app (U.obj (W.obj X)) ≫ G'.map (s.hom.app X) :=
    β.naturality (s.hom.app X)
  calc
    _ = (a.hom.app (W.obj X) ≫ β.app (U.obj (W.obj X))) ≫
        G'.map (s.hom.app X) := by rw [← Category.assoc, hCore]
    _ = a.hom.app (W.obj X) ≫
        (G.map (s.hom.app X) ≫ β.app (W'.obj X)) := by
      rw [Category.assoc, ← hRefinement]
    _ = _ := by simp only [Category.assoc]

end CategoryTheory.Functor
