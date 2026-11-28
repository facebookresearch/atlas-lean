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
# Functor comparisons after a source refinement

Let W : B → C, W′ : B → D, U : C → D, V : E → E′, F : C → E, and G : D → E′. Given natural
isomorphisms a : F⋙V≅U⋙G and s : W⋙U≅W′, associativity and whiskering give (W⋙F)⋙V≅W′⋙G.

At X its forward map is a_{W(X)} followed by G(s_X); the inverse reverses these two steps.
Compatible natural-transformation squares for a remain compatible after this source
refinement. The categories and their object and morphism universes are arbitrary.
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

/-- Let W : B → C, W′ : B → D, U : C → D, V : E → E′, F : C → E, and G : D → E′ be functors.
Natural isomorphisms a : F⋙V≅U⋙G and s : W⋙U≅W′ give a natural isomorphism (W⋙F)⋙V≅W′⋙G by
associators and whiskering. No size or additive assumptions on the categories are needed. -/
def precompositionComparisonIso : (W ⋙ F) ⋙ V ≅ W' ⋙ G :=
  Functor.associator W F V ≪≫ isoWhiskerLeft W a ≪≫
    (Functor.associator W U G).symm ≪≫ isoWhiskerRight s G

/-- Let W : B → C, W′ : B → D, U : C → D, V : E → E′, F : C → E, and G : D → E′ be functors, with
a : F⋙V≅U⋙G and s : W⋙U≅W′. The forward component at X∈B of the transported comparison is
a.hom at W(X) followed by G(s.hom at X). Its source is V(F(W(X))) and its target is G(W′(X)). -/
theorem precompositionComparisonIso_hom_app (X : B) :
    (precompositionComparisonIso W W' U V F G a s).hom.app X =
      a.hom.app (W.obj X) ≫ G.map (s.hom.app X) := by
  change (𝟙 _) ≫ a.hom.app (W.obj X) ≫ (𝟙 _) ≫ G.map (s.hom.app X) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Let W : B → C, W′ : B → D, U : C → D, V : E → E′, F : C → E, and G : D → E′, with a : F⋙V≅U⋙G
and s : W⋙U≅W′. The inverse component at X of (W⋙F)⋙V≅W′⋙G is G(s.inv at X) followed by a.inv
at W(X), from G(W′X) to V(F(WX)). -/
theorem precompositionComparisonIso_inv_app (X : B) :
    (precompositionComparisonIso W W' U V F G a s).inv.app X =
      G.map (s.inv.app X) ≫ a.inv.app (W.obj X) := by
  change ((G.map (s.inv.app X) ≫ (𝟙 _)) ≫ a.inv.app (W.obj X)) ≫ (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Let W : B → C, W′ : B → D, U : C → D, V : E → E′, F,F′ : C → E, and G,G′ : D → E′. Given a :
F⋙V≅U⋙G, a′ : F′⋙V≅U⋙G′, s : W⋙U≅W′, α : F → F′, and β : G → G′, assume
(α▷V)≫a′.hom=a.hom≫(U◁β). For the transported comparisons e,e′, ((W◁α)▷V)≫e′.hom=e.hom≫(W′◁β). -/
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
