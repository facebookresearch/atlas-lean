/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubordinateCoverWeakEquivalence
import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains.TwoSet
import MathlibExt.AlgebraicTopology.SingularHomology.Subspace.Basic
import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1EmbeddingCoproducts
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedBoundaryZeroRangeEmpty
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedSimplexBoundaryCollar
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedSimplexCellPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.OneCellOpenComplement
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatSDRPushoutWeakHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatBoundarySmallObject
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatRealizedCellClosedEmbedding
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyTransfiniteClosed
import MathlibExt.AlgebraicTopology.SingularSet.Coproducts
import MathlibExt.Topology.Category.TopCat.PushoutOpenRestriction
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Cardinal.Order

/-!
# Left properness of the selected TopCat model structure

The selected weak-homotopy model structure on TopCat is left proper in every
universe. Positive realized-boundary attachments are handled by two literal
open restrictions, the reviewed subordinate singular-cover theorem, and the
typed two-set simplicial pushout cube. Arbitrary selected cofibrations follow
from pushed-coproduct sequentialization, an explicit relative-cell cobase
ladder, closed-T1 limit stability, and the same-source small-object retract.

Only the scoped selected-model instance is exposed. No right-properness,
global cobase/transfinite/retract closure, localization, or CSS statement is
made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory

namespace TopCatLeftProperProof

private def principalSegToInitialSeg
    {A : Type u₁} {B : Type u₂} [Preorder A] [Preorder B]
    (p : A <i B) : A ≤i B where
  toRelEmbedding := p.toRelEmbedding
  mem_range_of_rel' a _b h := p.mem_range_iff_rel.2 (h.trans (p.lt_top a))

private noncomputable abbrev boundaryCell (n : ℕ) :=
  SSet.toTop.{u}.map (SSet.boundary.{u} n).ι

private noncomputable abbrev I : MorphismProperty TopCat.{u} :=
  TopCat.realizedBoundaryInclusions.{u}

private noncomputable abbrev W : MorphismProperty TopCat.{u} :=
  TopCat.weakHomotopyEquivalences.{u}

private def Q : MorphismProperty TopCat.{u} :=
  fun _ _ i ↦ (W.{u} : MorphismProperty TopCat.{u}).IsStableUnderCobaseChangeAlong i

private def P : MorphismProperty TopCat.{u} :=
  (Q.{u} : MorphismProperty TopCat.{u}) ⊓ TopCat.closedT1Embeddings.{u}

private def S : MorphismProperty TopCat.{u} :=
  (coproducts.{u} (I.{u} : MorphismProperty TopCat.{u})).pushouts

private theorem hasColimitsOfShapeCompleteLattice
    (K : Type w) [Category.{v} K] (J : Type u) [CompleteLattice J] :
    HasColimitsOfShape K J where
  has_colimit F :=
    (Preorder.hasColimit_iff_hasLUB F).2
      ⟨⨆ k, F.obj k, by
        constructor
        · rintro x ⟨k, rfl⟩
          exact le_iSup (fun k ↦ F.obj k) k
        · intro b hb
          exact iSup_le (fun k ↦ hb ⟨k, rfl⟩)⟩

private theorem hasColimitsOfShapeWellFoundedOrderTop
    (K : Type w) [Category.{v} K] (J : Type u)
    [LinearOrder J] [OrderTop J] [WellFoundedLT J] :
    HasColimitsOfShape K J where
  has_colimit F := by
    let s : Set J := upperBounds (Set.range F.obj)
    have hs : s.Nonempty := by
      refine ⟨⊤, ?_⟩
      rintro x ⟨k, rfl⟩
      exact le_top
    let m : J := WellFoundedLT.min s hs
    apply (Preorder.hasColimit_iff_hasLUB F).2
    exact ⟨m, WellFounded.min_mem wellFounded_lt s hs,
      fun b hb ↦ WellFoundedLT.min_le hb⟩

private theorem hasColimitsOfShapeProd
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (K : Type w₁) [Category.{w₂} K]
    [HasColimitsOfShape K A] [HasColimitsOfShape K B] :
    HasColimitsOfShape K (A × B) where
  has_colimit F := by
    let F₁ : K ⥤ A := F ⋙ CategoryTheory.Prod.fst A B
    let F₂ : K ⥤ B := F ⋙ CategoryTheory.Prod.snd A B
    let c : Cocone F := {
      pt := (colimit F₁, colimit F₂)
      ι :=
        { app := fun k ↦ (colimit.ι F₁ k, colimit.ι F₂ k)
          naturality := fun _ _ f ↦ by
            ext
            · simpa only [prod_comp, Functor.const_obj_map, prod_id,
                Category.comp_id, F₁, Functor.comp_map,
                CategoryTheory.Prod.fst_map] using colimit.w F₁ f
            · simpa only [prod_comp, Functor.const_obj_map, prod_id,
                Category.comp_id, F₂, Functor.comp_map,
                CategoryTheory.Prod.snd_map] using colimit.w F₂ f } }
    let proj₁ (s : Cocone F) : Cocone F₁ :=
      { pt := s.pt.1
        ι :=
          { app := fun k ↦ (s.ι.app k).1
            naturality := fun _ _ f ↦ by
              simp only [Functor.const_obj_map]
              have h : F₁.map f ≫ (s.ι.app _).1 = (s.ι.app _).1 := by
                simpa only [prod_comp, F₁, Functor.comp_map,
                  CategoryTheory.Prod.fst_map] using
                  congrArg Prod.fst (s.w f)
              exact h.trans (Category.comp_id _).symm } }
    let proj₂ (s : Cocone F) : Cocone F₂ :=
      { pt := s.pt.2
        ι :=
          { app := fun k ↦ (s.ι.app k).2
            naturality := fun _ _ f ↦ by
              simp only [Functor.const_obj_map]
              have h : F₂.map f ≫ (s.ι.app _).2 = (s.ι.app _).2 := by
                simpa only [prod_comp, F₂, Functor.comp_map,
                  CategoryTheory.Prod.snd_map] using
                  congrArg Prod.snd (s.w f)
              exact h.trans (Category.comp_id _).symm } }
    refine ⟨⟨c, ?_⟩⟩
    refine
      { desc := fun s ↦
          ((colimit.isColimit F₁).desc (proj₁ s),
            (colimit.isColimit F₂).desc (proj₂ s))
        fac := fun s k ↦ by
          ext
          · exact (colimit.isColimit F₁).fac _ k
          · exact (colimit.isColimit F₂).fac _ k
        uniq := fun s m hm ↦ by
          apply CategoryTheory.Prod.hom_ext
          · change m.1 = (colimit.isColimit F₁).desc (proj₁ s)
            apply (colimit.isColimit F₁).hom_ext
            intro k
            calc
              colimit.ι F₁ k ≫ m.1 = (s.ι.app k).1 := by
                simpa only [prod_comp] using congrArg Prod.fst (hm k)
              _ = colimit.ι F₁ k ≫
                    (colimit.isColimit F₁).desc (proj₁ s) :=
                ((colimit.isColimit F₁).fac (proj₁ s) k).symm
          · change m.2 = (colimit.isColimit F₂).desc (proj₂ s)
            apply (colimit.isColimit F₂).hom_ext
            intro k
            calc
              colimit.ι F₂ k ≫ m.2 = (s.ι.app k).2 := by
                simpa only [prod_comp] using congrArg Prod.snd (hm k)
              _ = colimit.ι F₂ k ≫
                    (colimit.isColimit F₂).desc (proj₂ s) :=
                ((colimit.isColimit F₂).fac (proj₂ s) k).symm }

private def prodCoconeFst
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {K : Type w₁} [Category.{w₂} K] {F : K ⥤ A × B}
    (c : Cocone F) : Cocone (F ⋙ CategoryTheory.Prod.fst A B) :=
  { pt := c.pt.1
    ι :=
      { app := fun k ↦ (c.ι.app k).1
        naturality := fun _ _ f ↦ by
          simp only [Functor.const_obj_map]
          have h : (F ⋙ CategoryTheory.Prod.fst A B).map f ≫
              (c.ι.app _).1 = (c.ι.app _).1 := by
            simpa only [prod_comp, Functor.comp_map,
              CategoryTheory.Prod.fst_map] using
              congrArg Prod.fst (c.w f)
          exact h.trans (Category.comp_id _).symm } }

private noncomputable def prodCoconeFst_isColimit
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {K : Type w₁} [Category.{w₂} K] {F : K ⥤ A × B}
    (c : Cocone F) (hc : IsColimit c) : IsColimit (prodCoconeFst c) := by
  let pairCocone (s : Cocone (F ⋙ CategoryTheory.Prod.fst A B)) : Cocone F :=
    { pt := (s.pt, c.pt.2)
      ι :=
        { app := fun k ↦ (s.ι.app k, (c.ι.app k).2)
          naturality := fun _ _ f ↦ by
            ext
            · simpa only [prod_comp, Functor.const_obj_map, prod_id,
                Category.comp_id, Functor.comp_map,
                CategoryTheory.Prod.fst_map] using s.w f
            · simpa only [prod_comp, Functor.const_obj_map, prod_id,
                Category.comp_id] using congrArg Prod.snd (c.w f) } }
  refine
    { desc := fun s ↦ (hc.desc (pairCocone s)).1
      fac := fun s k ↦ by
        change (c.ι.app k).1 ≫ (hc.desc (pairCocone s)).1 = s.ι.app k
        simpa only [prod_comp] using
          congrArg Prod.fst (hc.fac (pairCocone s) k)
      uniq := fun s m hm ↦ by
        let m₁ : c.pt ⟶ (s.pt, c.pt.2) := (m, 𝟙 c.pt.2)
        let m₂ : c.pt ⟶ (s.pt, c.pt.2) :=
          ((hc.desc (pairCocone s)).1, 𝟙 c.pt.2)
        have heq : m₁ = m₂ := hc.hom_ext (fun k ↦ by
          apply CategoryTheory.Prod.hom_ext
          · calc
              (c.ι.app k).1 ≫ m = s.ι.app k := by
                exact hm k
              _ = (c.ι.app k).1 ≫ (hc.desc (pairCocone s)).1 := by
                simpa only [prod_comp] using
                  (congrArg Prod.fst (hc.fac (pairCocone s) k)).symm
          · simp [m₁, m₂])
        change m = (hc.desc (pairCocone s)).1
        exact congrArg Prod.fst heq }

private def prodCoconeSnd
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {K : Type w₁} [Category.{w₂} K] {F : K ⥤ A × B}
    (c : Cocone F) : Cocone (F ⋙ CategoryTheory.Prod.snd A B) :=
  { pt := c.pt.2
    ι :=
      { app := fun k ↦ (c.ι.app k).2
        naturality := fun _ _ f ↦ by
          simp only [Functor.const_obj_map]
          have h : (F ⋙ CategoryTheory.Prod.snd A B).map f ≫
              (c.ι.app _).2 = (c.ι.app _).2 := by
            simpa only [prod_comp, Functor.comp_map,
              CategoryTheory.Prod.snd_map] using
              congrArg Prod.snd (c.w f)
          exact h.trans (Category.comp_id _).symm } }

private noncomputable def prodCoconeSnd_isColimit
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {K : Type w₁} [Category.{w₂} K] {F : K ⥤ A × B}
    (c : Cocone F) (hc : IsColimit c) : IsColimit (prodCoconeSnd c) := by
  let pairCocone (s : Cocone (F ⋙ CategoryTheory.Prod.snd A B)) : Cocone F :=
    { pt := (c.pt.1, s.pt)
      ι :=
        { app := fun k ↦ ((c.ι.app k).1, s.ι.app k)
          naturality := fun _ _ f ↦ by
            ext
            · simpa only [prod_comp, Functor.const_obj_map, prod_id,
                Category.comp_id] using congrArg Prod.fst (c.w f)
            · simpa only [prod_comp, Functor.const_obj_map, prod_id,
                Category.comp_id, Functor.comp_map,
                CategoryTheory.Prod.snd_map] using s.w f } }
  refine
    { desc := fun s ↦ (hc.desc (pairCocone s)).2
      fac := fun s k ↦ by
        change (c.ι.app k).2 ≫ (hc.desc (pairCocone s)).2 = s.ι.app k
        simpa only [prod_comp] using
          congrArg Prod.snd (hc.fac (pairCocone s) k)
      uniq := fun s m hm ↦ by
        let m₁ : c.pt ⟶ (c.pt.1, s.pt) := (𝟙 c.pt.1, m)
        let m₂ : c.pt ⟶ (c.pt.1, s.pt) :=
          (𝟙 c.pt.1, (hc.desc (pairCocone s)).2)
        have heq : m₁ = m₂ := hc.hom_ext (fun k ↦ by
          apply CategoryTheory.Prod.hom_ext
          · simp [m₁, m₂]
          · calc
              (c.ι.app k).2 ≫ m = s.ι.app k := by
                exact hm k
              _ = (c.ι.app k).2 ≫ (hc.desc (pairCocone s)).2 := by
                simpa only [prod_comp] using
                  (congrArg Prod.snd (hc.fac (pairCocone s) k)).symm)
        change m = (hc.desc (pairCocone s)).2
        exact congrArg Prod.snd heq }

private def prodIsoSnd
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {X Y : A × B} (e : X ≅ Y) : X.2 ≅ Y.2 where
  hom := e.hom.2
  inv := e.inv.2
  hom_inv_id := congrArg Prod.snd e.hom_inv_id
  inv_hom_id := congrArg Prod.snd e.inv_hom_id

private abbrev iterationSndIncl
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (J : Type w₁) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [HasIterationOfShape J (A × B)] (Phi : SmallObject.SuccStruct (A × B))
    (j : J) : ((Phi.iterationFunctor J).obj j).2 ⟶ (Phi.iteration J).2 :=
  ((Phi.iterationCocone J).ι.app j).2

set_option backward.isDefEq.respectTransparency false in
private theorem iterationSndIncl_naturality
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (J : Type w₁) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [HasIterationOfShape J (A × B)] (Phi : SmallObject.SuccStruct (A × B))
    {i j : J} (f : i ⟶ j) :
    ((Phi.iterationFunctor J).map f).2 ≫ iterationSndIncl J Phi j =
      iterationSndIncl J Phi i := by
  simpa only [prod_comp] using
    congrArg Prod.snd ((Phi.iterationCocone J).w f)

private abbrev underCarrierDiagram
    {C : Type u₁} [Category.{v₁} C] {X : C}
    {K : Type w₁} [Category.{w₂} K] (F : K ⥤ Under X) : K ⥤ C where
  obj k := (F.obj k).right
  map f := (F.map f).right

private abbrev underCoconeCarrier
    {C : Type u₁} [Category.{v₁} C] {X : C}
    {K : Type w₁} [Category.{w₂} K] {F : K ⥤ Under X}
    (c : Cocone F) : Cocone (underCarrierDiagram F) :=
  { pt := c.pt.right
    ι :=
      { app := fun k ↦ (c.ι.app k).right
        naturality := fun _ _ f ↦ by
          dsimp
          rw [Category.comp_id]
          simpa only [Under.comp_right] using
            congrArg Under.Hom.right (c.w f) } }

private noncomputable def underCoconeCarrier_isColimit_of_orderBot
    {C : Type u₁} [Category.{v₁} C] {X : C}
    {K : Type w₁} [Preorder K] [OrderBot K]
    {F : K ⥤ Under X} (c : Cocone F) (hc : IsColimit c) :
    IsColimit (underCoconeCarrier c) := by
  let underCocone (s : Cocone (underCarrierDiagram F)) : Cocone F :=
    { pt := Under.mk ((F.obj ⊥).hom ≫ s.ι.app ⊥)
      ι :=
        { app := fun k ↦ Under.homMk (s.ι.app k) (by
            have hF := Under.w (F.map (homOfLE bot_le : ⊥ ⟶ k))
            have hs := s.w (homOfLE bot_le : ⊥ ⟶ k)
            have hw : (F.obj k).hom ≫ s.ι.app k =
                (F.obj ⊥).hom ≫ s.ι.app ⊥ := by
              calc
                (F.obj k).hom ≫ s.ι.app k =
                  ((F.obj ⊥).hom ≫ (F.map (homOfLE bot_le : ⊥ ⟶ k)).right) ≫
                    s.ι.app k := by rw [hF]
                _ = (F.obj ⊥).hom ≫ s.ι.app ⊥ := by
                  rw [Category.assoc, hs]
            simpa using hw)
          naturality := fun _ _ f ↦ by
            apply Under.UnderMorphism.ext
            change (F.map f).right ≫ s.ι.app _ = s.ι.app _ ≫ 𝟙 _
            have hn : (F.map f).right ≫ s.ι.app _ = s.ι.app _ := s.w f
            exact hn.trans (Category.comp_id _).symm } }
  refine
    { desc := fun s ↦ (hc.desc (underCocone s)).right
      fac := fun s k ↦ by
        change (c.ι.app k).right ≫ (hc.desc (underCocone s)).right = s.ι.app k
        have hfac := congrArg Under.Hom.right (hc.fac (underCocone s) k)
        have happ : ((underCocone s).ι.app k).right = s.ι.app k := by
          rfl
        exact hfac.trans happ
      uniq := fun s m hm ↦ by
        change c.pt.right ⟶ s.pt at m
        change ∀ j, (c.ι.app j).right ≫ m = s.ι.app j at hm
        have hcomm : c.pt.hom ≫ m = (underCocone s).pt.hom := by
          have hc₀ : (F.obj ⊥).hom ≫ (c.ι.app ⊥).right = c.pt.hom := by
            exact Under.w (c.ι.app ⊥)
          have hw : c.pt.hom ≫ m = (F.obj ⊥).hom ≫ s.ι.app ⊥ := by
            calc
              c.pt.hom ≫ m = ((F.obj ⊥).hom ≫ (c.ι.app ⊥).right) ≫ m := by
                rw [hc₀]
              _ = (F.obj ⊥).hom ≫ s.ι.app ⊥ := by
                rw [Category.assoc, hm ⊥]
          simpa [underCocone] using hw
        let m₁ : c.pt ⟶ (underCocone s).pt := Under.homMk m hcomm
        let m₂ : c.pt ⟶ (underCocone s).pt := hc.desc (underCocone s)
        have heq : m₁ = m₂ := hc.hom_ext (fun k ↦ by
          apply Under.UnderMorphism.ext
          calc
            (c.ι.app k).right ≫ m = s.ι.app k := hm k
            _ = (c.ι.app k).right ≫ (hc.desc (underCocone s)).right := by
              have hfac := congrArg Under.Hom.right (hc.fac (underCocone s) k)
              have happ : ((underCocone s).ι.app k).right = s.ι.app k := by
                rfl
              exact happ.symm.trans hfac.symm)
        change m = (hc.desc (underCocone s)).right
        have hright := congrArg Under.Hom.right heq
        exact hright }

private abbrev factorizationCarrierDiagram
    {C : Type u₁} [Category.{v₁} C] {X Y : C} {q : X ⟶ Y}
    {A : Type u₂} [Category.{v₂} A]
    {K : Type w₁} [Category.{w₂} K]
    (F : K ⥤ A × Over (Under.mk q)) : K ⥤ C :=
  underCarrierDiagram
    (F ⋙ CategoryTheory.Prod.snd A (Over (Under.mk q)) ⋙
      Over.forget (Under.mk q))

private abbrev factorizationCarrierFunctor
    {C : Type u₁} [Category.{v₁} C] {X Y : C} (q : X ⟶ Y)
    (A : Type u₂) [Category.{v₂} A] :
    A × Over (Under.mk q) ⥤ C where
  obj Z := Z.2.left.right
  map f := f.2.left.right

private abbrev factorizationCarrierCocone
    {C : Type u₁} [Category.{v₁} C] {X Y : C} {q : X ⟶ Y}
    {A : Type u₂} [Category.{v₂} A]
    {K : Type w₁} [Category.{w₂} K]
    {F : K ⥤ A × Over (Under.mk q)} (c : Cocone F) :
    Cocone (factorizationCarrierDiagram F) :=
  underCoconeCarrier
    ((Over.forget (Under.mk q)).mapCocone (prodCoconeSnd c))

private noncomputable def factorizationCarrierCocone_isColimit_of_orderBot
    {C : Type u₁} [Category.{v₁} C] {X Y : C} {q : X ⟶ Y}
    {A : Type u₂} [Category.{v₂} A]
    {K : Type w₁} [Preorder K] [OrderBot K]
    [HasColimitsOfShape K (Under X)]
    {F : K ⥤ A × Over (Under.mk q)} (c : Cocone F) (hc : IsColimit c) :
    IsColimit (factorizationCarrierCocone c) := by
  let cD := prodCoconeSnd c
  let hcD : IsColimit cD := prodCoconeSnd_isColimit c hc
  let : HasColimit (F ⋙ CategoryTheory.Prod.snd A (Over (Under.mk q))) :=
    ⟨⟨cD, hcD⟩⟩
  let cU := (Over.forget (Under.mk q)).mapCocone cD
  let hcU : IsColimit cU := isColimitOfPreserves (Over.forget (Under.mk q)) hcD
  exact underCoconeCarrier_isColimit_of_orderBot cU hcU

private theorem coprod_map_mem_W
    {A B C D : TopCat.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (hf : W f) (hg : W g) : W (coprod.map f g) := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj A) := TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj B) := TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj C) := TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj D) := TopCat.toSSet_obj_kanComplex _
  have hf' : SSet.realizationWeakEquivalences (TopCat.toSSet.map f) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp hf
  have hg' : SSet.realizationWeakEquivalences (TopCat.toSSet.map g) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp hg
  have hCoprod : SSet.realizationWeakEquivalences
      (coprod.map (TopCat.toSSet.map f) (TopCat.toSSet.map g)) :=
    SSet.coprod_map_mem_realizationWeakEquivalences _ _ hf' hg'
  let c₁ := coprodComparison TopCat.toSSet A C
  let c₂ := coprodComparison TopCat.toSSet B D
  let _ : IsIso c₁ := inferInstance
  let _ : IsIso c₂ := inferInstance
  have hComp : SSet.realizationWeakEquivalences
      (c₁ ≫ TopCat.toSSet.map (coprod.map f g)) := by
    rw [coprodComparison_natural]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hCoprod
      (SSet.realizationWeakEquivalences.of_isIso c₂)
  have hMap : SSet.realizationWeakEquivalences
      (TopCat.toSSet.map (coprod.map f g)) :=
    (SSet.realizationWeakEquivalences.cancel_left_of_respectsIso c₁ _).mp hComp
  let _ : SSet.KanComplex (TopCat.toSSet.obj (A ⨿ C)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj (B ⨿ D)) :=
    TopCat.toSSet_obj_kanComplex _
  change TopCat.weakHomotopyEquivalences (coprod.map f g)
  rw [TopCat.mem_weakHomotopyEquivalences_iff]
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr hMap

private structure BoundaryOneCellSquare (n : ℕ) where
  X : TopCat.{u}
  Y : TopCat.{u}
  f : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) ⟶ X
  f' : SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ Y
  j : X ⟶ Y
  isPushout : IsPushout (boundaryCell n) f f' j

private structure BoundaryOneCellAttachmentCube (n : ℕ) where
  upper : BoundaryOneCellSquare.{u} n
  X' : TopCat.{u}
  Y' : TopCat.{u}
  h : upper.X ⟶ X'
  j' : X' ⟶ Y'
  k : upper.Y ⟶ Y'
  lowerPushout : IsPushout upper.j h k j'

private theorem BoundaryOneCellAttachmentCube.outerPushout {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    IsPushout (boundaryCell n) (c.upper.f ≫ c.h)
      (c.upper.f' ≫ c.k) c.j' :=
  c.upper.isPushout.paste_vert c.lowerPushout

private noncomputable def realizedBoundaryZero_isInitial :
    IsInitial (SSet.toTop.obj (SSet.boundary.{u} 0 : SSet.{u})) := by
  let _ : PreservesColimits SSet.toTop.{u} :=
    _root_.sSetTopAdj.leftAdjoint_preservesColimits
  have hInitS : IsInitial (SSet.boundary 0 : SSet.{u}) := by
    rw [SSet.boundary_zero]
    exact SSet.Subcomplex.isInitialBot
  exact hInitS.isInitialObj SSet.toTop _

private theorem boundaryZeroCubeGluing
    (c : BoundaryOneCellAttachmentCube.{u} 0) (hh : W c.h) : W c.k := by
  let D : TopCat.{u} := SSet.toTop.obj (Δ[0] : SSet.{u})
  let hInit : IsInitial (SSet.toTop.obj (SSet.boundary.{u} 0 : SSet.{u})) :=
    realizedBoundaryZero_isInitial
  have hBoundary : boundaryCell.{u} 0 = hInit.to D := hInit.hom_ext _ _
  have hAttach : c.upper.f = hInit.to c.upper.X := hInit.hom_ext _ _
  have hAttach' : c.upper.f ≫ c.h = hInit.to c.X' := hInit.hom_ext _ _
  have stdUpper : IsPushout (boundaryCell 0) c.upper.f
      (coprod.inl : D ⟶ D ⨿ c.upper.X) (coprod.inr : c.upper.X ⟶ D ⨿ c.upper.X) := by
    rw [hBoundary, hAttach]
    exact IsPushout.of_is_coproduct (coprodIsCoprod D c.upper.X) hInit
  have stdOuter : IsPushout (boundaryCell 0) (c.upper.f ≫ c.h)
      (coprod.inl : D ⟶ D ⨿ c.X') (coprod.inr : c.X' ⟶ D ⨿ c.X') := by
    rw [hBoundary, hAttach']
    exact IsPushout.of_is_coproduct (coprodIsCoprod D c.X') hInit
  let eY : c.upper.Y ≅ D ⨿ c.upper.X :=
    c.upper.isPushout.isoIsPushout D c.upper.X stdUpper
  let eY' : c.Y' ≅ D ⨿ c.X' :=
    c.outerPushout.isoIsPushout D c.X' stdOuter
  have hcomm : c.k ≫ eY'.hom = eY.hom ≫ coprod.map (𝟙 D) c.h := by
    apply c.upper.isPushout.hom_ext
    · calc
        c.upper.f' ≫ c.k ≫ eY'.hom =
            (c.upper.f' ≫ c.k) ≫ eY'.hom := (Category.assoc _ _ _).symm
        _ = coprod.inl := by
          change (c.upper.f' ≫ c.k) ≫
            (c.outerPushout.isoIsPushout D c.X' stdOuter).hom = coprod.inl
          exact c.outerPushout.inl_isoIsPushout_hom D c.X' stdOuter
        _ = coprod.inl ≫ coprod.map (𝟙 D) c.h := by
          simpa only [Category.id_comp] using
            (coprod.inl_map (𝟙 D) c.h).symm
        _ = (c.upper.f' ≫ eY.hom) ≫ coprod.map (𝟙 D) c.h := by
          exact congrArg (· ≫ coprod.map (𝟙 D) c.h)
            (c.upper.isPushout.inl_isoIsPushout_hom D c.upper.X stdUpper).symm
        _ = c.upper.f' ≫ eY.hom ≫ coprod.map (𝟙 D) c.h :=
          Category.assoc _ _ _
    · calc
        c.upper.j ≫ c.k ≫ eY'.hom =
            (c.upper.j ≫ c.k) ≫ eY'.hom := (Category.assoc _ _ _).symm
        _ = (c.h ≫ c.j') ≫ eY'.hom := by rw [c.lowerPushout.w]
        _ = c.h ≫ (c.j' ≫ eY'.hom) := Category.assoc _ _ _
        _ = c.h ≫ coprod.inr := by
          apply congrArg (c.h ≫ ·)
          change c.j' ≫ (c.outerPushout.isoIsPushout D c.X' stdOuter).hom =
            coprod.inr
          exact c.outerPushout.inr_isoIsPushout_hom D c.X' stdOuter
        _ = coprod.inr ≫ coprod.map (𝟙 D) c.h :=
          (coprod.inr_map (𝟙 D) c.h).symm
        _ = (c.upper.j ≫ eY.hom) ≫ coprod.map (𝟙 D) c.h := by
          exact congrArg (· ≫ coprod.map (𝟙 D) c.h)
            (c.upper.isPushout.inr_isoIsPushout_hom D c.upper.X stdUpper).symm
        _ = c.upper.j ≫ eY.hom ≫ coprod.map (𝟙 D) c.h :=
          Category.assoc _ _ _
  let e : Arrow.mk c.k ≅ Arrow.mk (coprod.map (𝟙 D) c.h) :=
    Arrow.isoMk eY eY' hcomm.symm
  have hCoprod : W (coprod.map (𝟙 D) c.h) :=
    coprod_map_mem_W (𝟙 D) c.h (W.id_mem D) hh
  exact (W.arrow_mk_iso_iff e).2 hCoprod

private noncomputable def boundaryBaryValue (n : ℕ) : ℝ :=
  ((((n + 1 : ℕ) : ℝ)))⁻¹

private noncomputable def boundaryThickeningLevel (n : ℕ) : ℝ :=
  boundaryBaryValue n / 2

private lemma boundaryBaryValue_pos (n : ℕ) : 0 < boundaryBaryValue n := by
  unfold boundaryBaryValue
  positivity

private lemma boundaryThickeningLevel_pos (n : ℕ) :
    0 < boundaryThickeningLevel n := by
  unfold boundaryThickeningLevel
  exact div_pos (boundaryBaryValue_pos n) (by norm_num)

private lemma boundaryThickeningLevel_lt_baryValue (n : ℕ) :
    boundaryThickeningLevel n < boundaryBaryValue n := by
  exact half_lt_self (boundaryBaryValue_pos n)

private lemma cutoff_realizedBarycenter (n : ℕ) :
    RealizedSimplexBoundaryCutoff.cutoff n (SSet.realizedBarycenter n) =
      boundaryBaryValue n := by
  unfold RealizedSimplexBoundaryCutoff.cutoff SSet.realizedBarycenter
  rw [Homeomorph.apply_symm_apply]
  obtain ⟨j, hj⟩ := StdSimplexRadialBoundary.exists_radMin_eq n
    (Convexity.StdSimplex.barycenter :
      Convexity.StdSimplex ℝ (Fin (n + 1)))
  rw [hj, Convexity.StdSimplex.weights_barycenter_apply,
    Fintype.card_fin]
  rfl

private abbrev boundaryNeighborhood (n : ℕ) :=
  {q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
    q ∈ RealizedSimplexBoundaryCutoff.thickening n
      (boundaryThickeningLevel n)}

private lemma boundaryNeighborhood_ne_barycenter (n : ℕ)
    (q : boundaryNeighborhood.{u} n) :
    q.val ≠ SSet.realizedBarycenter n := by
  intro hq
  have hmem := q.property
  change RealizedSimplexBoundaryCutoff.cutoff n q.val <
    boundaryThickeningLevel n at hmem
  rw [hq, cutoff_realizedBarycenter] at hmem
  exact (not_lt_of_ge (boundaryThickeningLevel_lt_baryValue n).le) hmem

private lemma boundaryNeighborhood_std_ne_barycenter (n : ℕ)
    (q : boundaryNeighborhood.{u} n) :
    ((SimplexCategory.mk n).toTopHomeo) q.val ≠
      Convexity.StdSimplex.barycenter := by
  intro hq
  apply boundaryNeighborhood_ne_barycenter n q
  apply (SimplexCategory.mk n).toTopHomeo.injective
  simpa [SSet.realizedBarycenter] using hq

private noncomputable def boundaryNeighborhoodToComplement (n : ℕ) :
    C(boundaryNeighborhood.{u} n,
      {q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
        q ≠ SSet.realizedBarycenter n}) where
  toFun q := ⟨q.val, boundaryNeighborhood_ne_barycenter n q⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

private noncomputable def boundaryNeighborhoodInclusion (n : ℕ) :
    TopCat.of (boundaryNeighborhood.{u} n) ⟶
      SSet.toTop.obj (Δ[n] : SSet.{u}) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

private noncomputable def boundaryNeighborhoodRetraction (n : ℕ) :
    TopCat.of (boundaryNeighborhood.{u} n) ⟶
      SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}) :=
  TopCat.ofHom ((SSet.realizedBoundaryRadialRetraction n).hom.comp
    (boundaryNeighborhoodToComplement n))

private noncomputable def boundaryNeighborhoodToStdComplement (n : ℕ) :
    C(boundaryNeighborhood.{u} n,
      {x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter}) where
  toFun q := ⟨((SimplexCategory.mk n).toTopHomeo) q.val,
    boundaryNeighborhood_std_ne_barycenter n q⟩
  continuous_toFun := Continuous.subtype_mk
    ((SimplexCategory.mk n).toTopHomeo.continuous.comp continuous_subtype_val) _

private noncomputable def stdComplementToRealized (n : ℕ) :
    C({x : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        x ≠ Convexity.StdSimplex.barycenter},
      SSet.toTop.obj (Δ[n] : SSet.{u})) where
  toFun q := (SimplexCategory.mk n).toTopHomeo.symm q.val
  continuous_toFun :=
    (SimplexCategory.mk n).toTopHomeo.symm.continuous.comp continuous_subtype_val

private noncomputable def boundaryNeighborhoodHomotopyRaw (n : ℕ) :
    ContinuousMap.Homotopy
      ((stdComplementToRealized.{u} n).comp
        (boundaryNeighborhoodToStdComplement n))
      ((stdComplementToRealized.{u} n).comp
        ((StdSimplexRadialBoundary.radialMapComplement n).comp
          (boundaryNeighborhoodToStdComplement n))) :=
  (ContinuousMap.Homotopy.refl (stdComplementToRealized.{u} n)).comp
    ((StdSimplexRadialBoundary.radialHomotopy n).comp
      (ContinuousMap.Homotopy.refl (boundaryNeighborhoodToStdComplement.{u} n)))

private lemma boundaryNeighborhoodHomotopyRaw_zero (n : ℕ) :
    (stdComplementToRealized.{u} n).comp
        (boundaryNeighborhoodToStdComplement n) =
      (boundaryNeighborhoodInclusion n).hom := by
  ext q
  exact (SimplexCategory.mk n).toTopHomeo.symm_apply_apply q.val

private lemma boundaryNeighborhoodHomotopyRaw_one (n : ℕ) :
    (stdComplementToRealized.{u} n).comp
        ((StdSimplexRadialBoundary.radialMapComplement n).comp
          (boundaryNeighborhoodToStdComplement n)) =
      (boundaryNeighborhoodRetraction n ≫ boundaryCell n).hom := by
  ext q
  exact (SSet.realizedBoundaryRadialRetraction_ι_apply n
    (boundaryNeighborhoodToComplement n q)).symm

private noncomputable def boundaryNeighborhoodHomotopy (n : ℕ) :
    TopCat.Homotopy (boundaryNeighborhoodInclusion n)
      (boundaryNeighborhoodRetraction n ≫ boundaryCell n) :=
  ContinuousMap.Homotopy.cast (boundaryNeighborhoodHomotopyRaw.{u} n)
    (boundaryNeighborhoodHomotopyRaw_zero n)
    (boundaryNeighborhoodHomotopyRaw_one n)

private theorem boundaryNeighborhoodHomotopy_fixed
    (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj (SSet.boundary.{u} n : SSet.{u}))
    (hx : SSet.toTop.map (SSet.boundary.{u} n).ι x ∈
      RealizedSimplexBoundaryCutoff.thickening n
        (boundaryThickeningLevel n)) :
    boundaryNeighborhoodHomotopy n
      (t, ⟨SSet.toTop.map (SSet.boundary.{u} n).ι x, hx⟩) =
        SSet.toTop.map (SSet.boundary.{u} n).ι x := by
  obtain ⟨j, hj⟩ :=
    SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange n
      (SSet.toTop.map (SSet.boundary.{u} n).ι x) ⟨x, rfl⟩
  let qStd : {q : Convexity.StdSimplex ℝ (Fin (n + 1)) //
      q ≠ Convexity.StdSimplex.barycenter} :=
    ⟨((SimplexCategory.mk n).toTopHomeo)
      (SSet.toTop.map (SSet.boundary.{u} n).ι x),
      boundaryNeighborhood_std_ne_barycenter n
        ⟨SSet.toTop.map (SSet.boundary.{u} n).ι x, hx⟩⟩
  have hfix : StdSimplexRadialBoundary.homotopyPoint n t qStd.val qStd.property =
      qStd.val :=
    StdSimplexRadialBoundary.homotopyPoint_eq_of_has_zero n t qStd j (by
      simpa [qStd] using hj)
  change (SimplexCategory.mk n).toTopHomeo.symm
      (StdSimplexRadialBoundary.homotopyPoint n t qStd.val qStd.property) =
    SSet.toTop.map (SSet.boundary.{u} n).ι x
  rw [hfix]
  exact (SimplexCategory.mk n).toTopHomeo.symm_apply_apply _

private noncomputable def subordinateSetIso
    {X : TopCat.{u}} (A : Set X) :
    TopCat.toSSet.obj (TopCat.of A) ≅
      (AlgebraicTopology.subordinateSet A : SSet.{u}) := by
  let f : TopCat.toSSet.obj (TopCat.of A) ⟶ TopCat.toSSet.obj X :=
    TopCat.toSSet.map (AlgebraicTopology.subspaceIncl A)
  let _ : Mono f := AlgebraicTopology.mono_toSSet_map_subspaceIncl A
  let e₁ : TopCat.toSSet.obj (TopCat.of A) ≅
      (SSet.Subcomplex.range f : SSet.{u}) :=
    asIso (SSet.Subcomplex.toRange f)
  let e₂ : (SSet.Subcomplex.range f : SSet.{u}) ≅
      (AlgebraicTopology.subordinateSet A : SSet.{u}) :=
    SSet.Subcomplex.eqToIso
      (AlgebraicTopology.range_subspaceIncl_eq_subordinateSet A)
  exact e₁ ≪≫ e₂

private theorem subordinateSet_inter_isPushout
    {X : TopCat.{u}} (A B : Set X) :
    IsPushout
      (SSet.Subcomplex.homOfLE
        (AlgebraicTopology.subordinateSet_mono Set.inter_subset_left))
      (SSet.Subcomplex.homOfLE
        (AlgebraicTopology.subordinateSet_mono Set.inter_subset_right))
      (SSet.Subcomplex.homOfLE
        (show AlgebraicTopology.subordinateSet A ≤
          AlgebraicTopology.subordinateSet A ⊔
            AlgebraicTopology.subordinateSet B from le_sup_left))
      (SSet.Subcomplex.homOfLE
        (show AlgebraicTopology.subordinateSet B ≤
          AlgebraicTopology.subordinateSet A ⊔
            AlgebraicTopology.subordinateSet B from le_sup_right)) := by
  let sq : SSet.Subcomplex.BicartSq
      (AlgebraicTopology.subordinateSet (A ∩ B))
      (AlgebraicTopology.subordinateSet A)
      (AlgebraicTopology.subordinateSet B)
      (AlgebraicTopology.subordinateSet A ⊔
        AlgebraicTopology.subordinateSet B) :=
    { sup_eq := rfl
      inf_eq := (AlgebraicTopology.subordinateSet_inter A B).symm }
  exact sq.isPushout

private noncomputable def subordinateTwoCoverIso
    {X : TopCat.{u}} (A B : Set X) :
    ((AlgebraicTopology.subordinateSet A ⊔
      AlgebraicTopology.subordinateSet B :
        (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) ≅
      (AlgebraicTopology.subCxBoth A B : SSet.{u}) :=
  SSet.Subcomplex.eqToIso (AlgebraicTopology.subCxBoth_eq_sup A B).symm

private noncomputable def subordinateSetMap
    {X Y : TopCat.{u}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    (AlgebraicTopology.subordinateSet A : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet B : SSet.{u}) :=
  SSet.Subcomplex.lift
    ((AlgebraicTopology.subordinateSet A).ι ≫ TopCat.toSSet.map f) (by
      have hrange : SSet.Subcomplex.range
          ((AlgebraicTopology.subordinateSet A).ι ≫ TopCat.toSSet.map f) =
          (AlgebraicTopology.subordinateSet A).image (TopCat.toSSet.map f) := by
        rw [SSet.Subcomplex.image_eq_range]
      rw [hrange]
      exact AlgebraicTopology.subordinateSet_image_le f h)

private lemma subordinateSetMap_ι
    {X Y : TopCat.{u}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    subordinateSetMap f h ≫ (AlgebraicTopology.subordinateSet B).ι =
      (AlgebraicTopology.subordinateSet A).ι ≫ TopCat.toSSet.map f := by
  simp [subordinateSetMap]

private lemma subordinateSetIso_hom_ι
    {X : TopCat.{u}} (A : Set X) :
    (subordinateSetIso A).hom ≫ (AlgebraicTopology.subordinateSet A).ι =
      TopCat.toSSet.map (AlgebraicTopology.subspaceIncl A) := by
  simp [subordinateSetIso]

private lemma subordinateSetIso_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    (subordinateSetIso A).hom ≫ subordinateSetMap f h =
      TopCat.toSSet.map (AlgebraicTopology.subspaceMap f h) ≫
        (subordinateSetIso B).hom := by
  apply (cancel_mono
    (f := (AlgebraicTopology.subordinateSet B).ι)).mp
  calc
    ((subordinateSetIso A).hom ≫ subordinateSetMap f h) ≫
        (AlgebraicTopology.subordinateSet B).ι =
      (subordinateSetIso A).hom ≫
        (subordinateSetMap f h ≫
          (AlgebraicTopology.subordinateSet B).ι) := Category.assoc _ _ _
    _ = (subordinateSetIso A).hom ≫
        (AlgebraicTopology.subordinateSet A).ι ≫
          TopCat.toSSet.map f := by rw [subordinateSetMap_ι]
    _ = ((subordinateSetIso A).hom ≫
        (AlgebraicTopology.subordinateSet A).ι) ≫
          TopCat.toSSet.map f := (Category.assoc _ _ _).symm
    _ = TopCat.toSSet.map (AlgebraicTopology.subspaceIncl A) ≫
          TopCat.toSSet.map f := by rw [subordinateSetIso_hom_ι]
    _ = TopCat.toSSet.map
        (AlgebraicTopology.subspaceIncl A ≫ f) :=
      (TopCat.toSSet.map_comp _ _).symm
    _ = TopCat.toSSet.map
        (AlgebraicTopology.subspaceMap f h ≫
          AlgebraicTopology.subspaceIncl B) := by
      rw [AlgebraicTopology.subspaceMap_comp_subspaceIncl]
    _ = TopCat.toSSet.map (AlgebraicTopology.subspaceMap f h) ≫
        TopCat.toSSet.map (AlgebraicTopology.subspaceIncl B) :=
      TopCat.toSSet.map_comp _ _
    _ = TopCat.toSSet.map (AlgebraicTopology.subspaceMap f h) ≫
        ((subordinateSetIso B).hom ≫
          (AlgebraicTopology.subordinateSet B).ι) := by
      rw [subordinateSetIso_hom_ι]
    _ = (TopCat.toSSet.map (AlgebraicTopology.subspaceMap f h) ≫
        (subordinateSetIso B).hom) ≫
          (AlgebraicTopology.subordinateSet B).ι :=
      (Category.assoc _ _ _).symm

private theorem subordinateSetMap_mem_realizationWeakEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B)
    (hf : W (AlgebraicTopology.subspaceMap f h)) :
    SSet.realizationWeakEquivalences (subordinateSetMap f h) := by
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj (TopCat.of A)) := TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj (TopCat.of B)) := TopCat.toSSet_obj_kanComplex _
  have hSing : SSet.realizationWeakEquivalences
      (TopCat.toSSet.map (AlgebraicTopology.subspaceMap f h)) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp hf
  let e : Arrow.mk (TopCat.toSSet.map (AlgebraicTopology.subspaceMap f h)) ≅
      Arrow.mk (subordinateSetMap f h) :=
    Arrow.isoMk (subordinateSetIso A) (subordinateSetIso B)
      (subordinateSetIso_naturality f h)
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).1 hSing

private noncomputable def subordinateSupMap
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    ((AlgebraicTopology.subordinateSet A ⊔
      AlgebraicTopology.subordinateSet B :
        (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) ⟶
    ((AlgebraicTopology.subordinateSet A' ⊔
      AlgebraicTopology.subordinateSet B' :
        (TopCat.toSSet.obj Y).Subcomplex) : SSet.{u}) :=
  SSet.Subcomplex.lift
    ((AlgebraicTopology.subordinateSet A ⊔
      AlgebraicTopology.subordinateSet B).ι ≫ TopCat.toSSet.map f) (by
      have hImage :
          (AlgebraicTopology.subordinateSet A ⊔
            AlgebraicTopology.subordinateSet B).image (TopCat.toSSet.map f) ≤
          AlgebraicTopology.subordinateSet A' ⊔
            AlgebraicTopology.subordinateSet B' := by
        rw [SSet.Subcomplex.image_le_iff, SSet.Subcomplex.preimage_max]
        exact sup_le
          (((SSet.Subcomplex.image_le_iff
              (AlgebraicTopology.subordinateSet A) (TopCat.toSSet.map f)
              (AlgebraicTopology.subordinateSet A')).mp
            (AlgebraicTopology.subordinateSet_image_le f hA)).trans le_sup_left)
          (((SSet.Subcomplex.image_le_iff
              (AlgebraicTopology.subordinateSet B) (TopCat.toSSet.map f)
              (AlgebraicTopology.subordinateSet B')).mp
            (AlgebraicTopology.subordinateSet_image_le f hB)).trans le_sup_right)
      have hrange : SSet.Subcomplex.range
          ((AlgebraicTopology.subordinateSet A ⊔
              AlgebraicTopology.subordinateSet B).ι ≫
            TopCat.toSSet.map f) =
          (AlgebraicTopology.subordinateSet A ⊔
            AlgebraicTopology.subordinateSet B).image (TopCat.toSSet.map f) := by
        rw [SSet.Subcomplex.image_eq_range]
      rw [hrange]
      exact hImage)

private lemma subordinateSupMap_ι
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    subordinateSupMap f hA hB ≫
      (AlgebraicTopology.subordinateSet A' ⊔
        AlgebraicTopology.subordinateSet B').ι =
      (AlgebraicTopology.subordinateSet A ⊔
        AlgebraicTopology.subordinateSet B).ι ≫
        TopCat.toSSet.map f := by
  simp [subordinateSupMap]

private theorem mapsToInter
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    Set.MapsTo f (A ∩ B) (A' ∩ B') := fun _ hx ↦
  ⟨hA hx.1, hB hx.2⟩

private lemma subordinateSetMap_inter_left
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    SSet.Subcomplex.homOfLE
        (AlgebraicTopology.subordinateSet_mono Set.inter_subset_left) ≫
      subordinateSetMap f hA =
    subordinateSetMap f (mapsToInter f hA hB) ≫
      SSet.Subcomplex.homOfLE
        (AlgebraicTopology.subordinateSet_mono Set.inter_subset_left) := by
  let hI : Set.MapsTo f (A ∩ B) (A' ∩ B') := mapsToInter f hA hB
  apply (cancel_mono (f := (AlgebraicTopology.subordinateSet A').ι)).mp
  simp only [Category.assoc, subordinateSetMap_ι,
    SSet.Subcomplex.homOfLE_ι]
  rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]

private lemma subordinateSetMap_inter_right
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    SSet.Subcomplex.homOfLE
        (AlgebraicTopology.subordinateSet_mono Set.inter_subset_right) ≫
      subordinateSetMap f hB =
    subordinateSetMap f (mapsToInter f hA hB) ≫
      SSet.Subcomplex.homOfLE
        (AlgebraicTopology.subordinateSet_mono Set.inter_subset_right) := by
  let hI : Set.MapsTo f (A ∩ B) (A' ∩ B') := mapsToInter f hA hB
  apply (cancel_mono (f := (AlgebraicTopology.subordinateSet B').ι)).mp
  simp only [Category.assoc, subordinateSetMap_ι,
    SSet.Subcomplex.homOfLE_ι]
  rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]

private lemma subordinateSetMap_sup_left
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    SSet.Subcomplex.homOfLE (show AlgebraicTopology.subordinateSet A ≤
        AlgebraicTopology.subordinateSet A ⊔
          AlgebraicTopology.subordinateSet B from le_sup_left) ≫
      subordinateSupMap f hA hB =
    subordinateSetMap f hA ≫
      SSet.Subcomplex.homOfLE
        (show AlgebraicTopology.subordinateSet A' ≤
          AlgebraicTopology.subordinateSet A' ⊔
            AlgebraicTopology.subordinateSet B' from le_sup_left) := by
  apply (cancel_mono (f :=
    (AlgebraicTopology.subordinateSet A' ⊔
      AlgebraicTopology.subordinateSet B').ι)).mp
  simp [Category.assoc, subordinateSetMap_ι, subordinateSupMap_ι]

private lemma subordinateSetMap_sup_right
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    SSet.Subcomplex.homOfLE (show AlgebraicTopology.subordinateSet B ≤
        AlgebraicTopology.subordinateSet A ⊔
          AlgebraicTopology.subordinateSet B from le_sup_right) ≫
      subordinateSupMap f hA hB =
    subordinateSetMap f hB ≫
      SSet.Subcomplex.homOfLE
        (show AlgebraicTopology.subordinateSet B' ≤
          AlgebraicTopology.subordinateSet A' ⊔
            AlgebraicTopology.subordinateSet B' from le_sup_right) := by
  apply (cancel_mono (f :=
    (AlgebraicTopology.subordinateSet A' ⊔
      AlgebraicTopology.subordinateSet B').ι)).mp
  simp [Category.assoc, subordinateSetMap_ι, subordinateSupMap_ι]

private theorem subordinateSupMap_mem_realizationWeakEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B')
    (hWA : W (AlgebraicTopology.subspaceMap f hA))
    (hWB : W (AlgebraicTopology.subspaceMap f hB))
    (hWI : W (AlgebraicTopology.subspaceMap f (mapsToInter f hA hB))) :
    SSet.realizationWeakEquivalences (subordinateSupMap f hA hB) := by
  let i₀ : (AlgebraicTopology.subordinateSet (A ∩ B) : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet A : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (AlgebraicTopology.subordinateSet_mono Set.inter_subset_left)
  let g₀ : (AlgebraicTopology.subordinateSet (A ∩ B) : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet B : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (AlgebraicTopology.subordinateSet_mono Set.inter_subset_right)
  let p₀ : (AlgebraicTopology.subordinateSet A : SSet.{u}) ⟶
      ((AlgebraicTopology.subordinateSet A ⊔
        AlgebraicTopology.subordinateSet B :
          (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (show AlgebraicTopology.subordinateSet A ≤
      AlgebraicTopology.subordinateSet A ⊔ AlgebraicTopology.subordinateSet B from
      le_sup_left)
  let q₀ : (AlgebraicTopology.subordinateSet B : SSet.{u}) ⟶
      ((AlgebraicTopology.subordinateSet A ⊔
        AlgebraicTopology.subordinateSet B :
          (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (show AlgebraicTopology.subordinateSet B ≤
      AlgebraicTopology.subordinateSet A ⊔ AlgebraicTopology.subordinateSet B from
      le_sup_right)
  let i₁ : (AlgebraicTopology.subordinateSet (A' ∩ B') : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet A' : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (AlgebraicTopology.subordinateSet_mono Set.inter_subset_left)
  let g₁ : (AlgebraicTopology.subordinateSet (A' ∩ B') : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet B' : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (AlgebraicTopology.subordinateSet_mono Set.inter_subset_right)
  let p₁ : (AlgebraicTopology.subordinateSet A' : SSet.{u}) ⟶
      ((AlgebraicTopology.subordinateSet A' ⊔
        AlgebraicTopology.subordinateSet B' :
          (TopCat.toSSet.obj Y).Subcomplex) : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (show AlgebraicTopology.subordinateSet A' ≤
      AlgebraicTopology.subordinateSet A' ⊔ AlgebraicTopology.subordinateSet B' from
      le_sup_left)
  let q₁ : (AlgebraicTopology.subordinateSet B' : SSet.{u}) ⟶
      ((AlgebraicTopology.subordinateSet A' ⊔
        AlgebraicTopology.subordinateSet B' :
          (TopCat.toSSet.obj Y).Subcomplex) : SSet.{u}) :=
    SSet.Subcomplex.homOfLE
    (show AlgebraicTopology.subordinateSet B' ≤
      AlgebraicTopology.subordinateSet A' ⊔ AlgebraicTopology.subordinateSet B' from
      le_sup_right)
  let a : (AlgebraicTopology.subordinateSet (A ∩ B) : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet (A' ∩ B') : SSet.{u}) :=
    subordinateSetMap f (mapsToInter f hA hB)
  let b : (AlgebraicTopology.subordinateSet A : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet A' : SSet.{u}) := subordinateSetMap f hA
  let c : (AlgebraicTopology.subordinateSet B : SSet.{u}) ⟶
      (AlgebraicTopology.subordinateSet B' : SSet.{u}) := subordinateSetMap f hB
  let d : ((AlgebraicTopology.subordinateSet A ⊔
        AlgebraicTopology.subordinateSet B :
          (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) ⟶
      ((AlgebraicTopology.subordinateSet A' ⊔
        AlgebraicTopology.subordinateSet B' :
          (TopCat.toSSet.obj Y).Subcomplex) : SSet.{u}) :=
    subordinateSupMap f hA hB
  let _ : Cofibration i₀ := SSet.modelCategoryQuillen.cofibration_of_mono i₀
  let _ : Cofibration i₁ := SSet.modelCategoryQuillen.cofibration_of_mono i₁
  let _ : WeakEquivalence a := (weakEquivalence_iff a).mpr
    (subordinateSetMap_mem_realizationWeakEquivalences f _ hWI)
  let _ : WeakEquivalence b := (weakEquivalence_iff b).mpr
    (subordinateSetMap_mem_realizationWeakEquivalences f _ hWA)
  let _ : WeakEquivalence c := (weakEquivalence_iff c).mpr
    (subordinateSetMap_mem_realizationWeakEquivalences f _ hWB)
  have hd : WeakEquivalence d :=
    HomotopicalAlgebra.weakEquivalence_map_of_isPushouts_of_cofibrant
      (i := i₀) (g := g₀) (p := p₀) (q := q₀)
      (i' := i₁) (g' := g₁) (p' := p₁) (q' := q₁)
      (a := a) (b := b) (c := c) (d := d)
      (subordinateSet_inter_isPushout A B)
      (subordinateSet_inter_isPushout A' B')
      (by simpa [i₀, i₁, a, b] using subordinateSetMap_inter_left f hA hB)
      (by simpa [g₀, g₁, a, c] using subordinateSetMap_inter_right f hA hB)
      (by simpa [p₀, p₁, b, d] using subordinateSetMap_sup_left f hA hB)
      (by simpa [q₀, q₁, c, d] using subordinateSetMap_sup_right f hA hB)
  exact (weakEquivalence_iff d).mp hd

private def attachmentStageCell {J : Type u} :
    WithTop J → Option J :=
  WithTop.recTopCoe none some

private def cellAttachMap
    {C : Type u₁} [Category.{v₁} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) : A (c.π k) ⟶ Z.left.right :=
  c.cofan₁.inj k ≫ c.g₁ ≫ Z.left.hom

private def cellTargetMap
    {C : Type u₁} [Category.{v₁} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) : B (c.π k) ⟶ Y :=
  c.cofan₂.inj k ≫ c.g₂

private theorem cellAttach_comm
    {C : Type u₁} [Category.{v₁} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) :
    g (c.π k) ≫ cellTargetMap g c k =
      cellAttachMap g c k Z ≫ Z.hom.right := by
  have hz : Z.left.hom ≫ Z.hom.right = q := by
    exact Under.w Z.hom
  calc
    g (c.π k) ≫ cellTargetMap g c k =
        (g (c.π k) ≫ c.cofan₂.inj k) ≫ c.g₂ := by
      simp [cellTargetMap, Category.assoc]
    _ = (c.cofan₁.inj k ≫ c.m) ≫ c.g₂ := by rw [c.hm k]
    _ = c.cofan₁.inj k ≫ (c.m ≫ c.g₂) :=
      Category.assoc _ _ _
    _ = c.cofan₁.inj k ≫ (c.g₁ ≫ q) := by rw [c.isPushout.w]
    _ = (c.cofan₁.inj k ≫ c.g₁) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = (c.cofan₁.inj k ≫ c.g₁) ≫
        (Z.left.hom ≫ Z.hom.right) := by rw [hz]
    _ = cellAttachMap g c k Z ≫ Z.hom.right := by
      simp [cellAttachMap, Category.assoc]

private noncomputable def attachToTarget
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) :
    pushout (g (c.π k)) (cellAttachMap g c k Z) ⟶ Y :=
  pushout.desc (cellTargetMap g c k) Z.hom.right (cellAttach_comm g c k Z)

private noncomputable def attachUnder
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) : Under X :=
  Under.mk (Z.left.hom ≫
    pushout.inr (g (c.π k)) (cellAttachMap g c k Z))

private theorem attachUnder_toTarget
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) :
    (attachUnder g c k Z).hom ≫ attachToTarget g c k Z = q := by
  change (Z.left.hom ≫ pushout.inr _ _) ≫ pushout.desc _ _ _ = q
  rw [Category.assoc, pushout.inr_desc]
  exact Under.w Z.hom

private noncomputable def attachUnderHom
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) :
    attachUnder g c k Z ⟶ Under.mk q :=
  Under.homMk (attachToTarget g c k Z)
    (w := attachUnder_toTarget g c k Z)

private noncomputable def attachFactorization
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) : Over (Under.mk q) :=
  Over.mk (attachUnderHom g c k Z)

private noncomputable def attachFactorizationMap
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) :
    Z ⟶ attachFactorization g c k Z := by
  change Z ⟶ Over.mk (attachUnderHom g c k Z)
  let r : Z.left.right ⟶
      pushout (g (c.π k)) (cellAttachMap g c k Z) :=
    pushout.inr (g (c.π k)) (cellAttachMap g c k Z)
  let hUnder : Z.left ⟶ attachUnder g c k Z :=
    Under.homMk r (by rfl)
  exact Over.homMk hUnder (by
    apply Under.UnderMorphism.ext
    change pushout.inr (g (c.π k)) (cellAttachMap g c k Z) ≫
      attachToTarget g c k Z = Z.hom.right
    exact pushout.inr_desc _ _ _)

private theorem attachFactorizationMap_isPushout
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (k : c.ι) (Z : Over (Under.mk q)) :
    IsPushout (g (c.π k))
      (cellAttachMap g c k Z)
      (pushout.inl (g (c.π k))
        (cellAttachMap g c k Z))
      (attachFactorizationMap g c k Z).left.right := by
  change IsPushout (g (c.π k)) (cellAttachMap g c k Z)
    (pushout.inl _ _) (pushout.inr _ _)
  exact IsPushout.of_hasPushout _ _

private def initialFactorization
    {C : Type u₁} [Category.{v₁} C]
    {X Y : C} (q : X ⟶ Y) : Over (Under.mk q) :=
  Over.mk (Under.homMk (U := Under.mk (𝟙 X)) (V := Under.mk q) q (by simp))

private def terminalFactorization
    {C : Type u₁} [Category.{v₁} C]
    {X Y : C} (q : X ⟶ Y) : Over (Under.mk q) :=
  Over.mk (𝟙 (Under.mk q))

private def factorizationToTerminal
    {C : Type u₁} [Category.{v₁} C]
    {X Y : C} {q : X ⟶ Y} (Z : Over (Under.mk q)) :
    Z ⟶ terminalFactorization q :=
  Over.homMk Z.hom (by simp [terminalFactorization])

private theorem factorizationToTerminal_natural
    {C : Type u₁} [Category.{v₁} C]
    {X Y : C} {q : X ⟶ Y} {Z Z' : Over (Under.mk q)} (f : Z ⟶ Z') :
    f ≫ factorizationToTerminal Z' = factorizationToTerminal Z := by
  apply Over.OverMorphism.ext
  apply Under.UnderMorphism.ext
  change f.left.right ≫ Z'.hom.right = Z.hom.right
  have hw := Over.w f
  simpa only [Under.comp_right] using
    congrArg Under.Hom.right hw

private theorem initialFactorization_hom_ext
    {C : Type u₁} [Category.{v₁} C]
    {X Y : C} {q : X ⟶ Y} {Z : Over (Under.mk q)}
    (f g : initialFactorization q ⟶ Z) : f = g := by
  apply Over.OverMorphism.ext
  apply Under.UnderMorphism.ext
  have hf := Under.w f.left
  have hg := Under.w g.left
  simpa [initialFactorization] using hf.trans hg.symm

private structure CategoricalSuccStep
    {D : Type u₁} [Category.{v₁} D] (Z : D) where
  obj : D
  map : Z ⟶ obj

private theorem CategoricalSuccStep.map_comp_eqToIso_inv
    {D : Type u₁} [Category.{v₁} D] {Z : D}
    {s t : CategoricalSuccStep Z} (h : s = t) :
    t.map ≫ (eqToIso (congrArg CategoricalSuccStep.obj h)).inv = s.map := by
  cases h
  simp

private noncomputable def attachmentFactorizationStep
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (Z : WithTop c.ι × Over (Under.mk q)) : CategoricalSuccStep Z.2 :=
  (attachmentStageCell Z.1).elim
    { obj := Z.2, map := 𝟙 Z.2 }
    (fun k ↦
      { obj := attachFactorization g c k Z.2
        map := attachFactorizationMap g c k Z.2 })

private theorem attachmentFactorizationStep_eq_of_cell
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (Z : WithTop c.ι × Over (Under.mk q)) (k : c.ι)
    (h : attachmentStageCell Z.1 = some k) :
    attachmentFactorizationStep g c Z =
      ({ obj := attachFactorization g c k Z.2
         map := attachFactorizationMap g c k Z.2 } : CategoricalSuccStep Z.2) := by
  unfold attachmentFactorizationStep
  rw [h]
  rfl

private theorem attachmentFactorizationStep_obj_eq_of_cell
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (Z : WithTop c.ι × Over (Under.mk q)) (k : c.ι)
    (h : attachmentStageCell Z.1 = some k) :
    (attachmentFactorizationStep g c Z).obj = attachFactorization g c k Z.2 :=
  congrArg CategoricalSuccStep.obj (attachmentFactorizationStep_eq_of_cell g c Z k h)

private theorem attachmentFactorizationStep_map_eq_of_cell
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (Z : WithTop c.ι × Over (Under.mk q)) (k : c.ι)
    (h : attachmentStageCell Z.1 = some k) :
    attachFactorizationMap g c k Z.2 ≫
        (eqToIso (attachmentFactorizationStep_obj_eq_of_cell g c Z k h)).inv =
      (attachmentFactorizationStep g c Z).map := by
  exact CategoricalSuccStep.map_comp_eqToIso_inv
    (attachmentFactorizationStep_eq_of_cell g c Z k h)

private noncomputable def attachmentSuccStruct
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι]
    [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] :
    SmallObject.SuccStruct
      (WithTop c.ι × Over (Under.mk q)) where
  X₀ := (⊥, initialFactorization q)
  succ Z :=
    (Order.succ Z.1, (attachmentFactorizationStep g c Z).obj)
  toSucc Z :=
    (homOfLE (Order.le_succ Z.1), (attachmentFactorizationStep g c Z).map)

private theorem attachmentSuccStruct_toSucc_carrier_mem
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι] [SuccOrder (WithTop c.ι)]
    (T : MorphismProperty C) (hg : ∀ i, T (g i))
    (Z : WithTop c.ι × Over (Under.mk q)) (k : c.ι)
    (h : attachmentStageCell Z.1 = some k) :
    T.pushouts ((attachmentSuccStruct g c).toSucc Z).2.left.right := by
  change T.pushouts ((attachmentFactorizationStep g c Z).map.left.right)
  have hstep := attachmentFactorizationStep_eq_of_cell g c Z k h
  rw [hstep]
  exact T.pushouts_mk (attachFactorizationMap_isPushout g c k Z.2).flip
    (hg (c.π k))

private theorem attachmentIteration_stage_eq
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι]
    [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)]
    [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (j : WithTop c.ι) :
    (((attachmentSuccStruct g c).iterationFunctor
      (WithTop c.ι)).obj j).1 = j := by
  let J := WithTop c.ι
  let Φ := attachmentSuccStruct g c
  let F := Φ.iterationFunctor J
  change (F.obj j).1 = j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      obtain rfl := hj.eq_bot
      have he : (F.obj ⊥).1 = Φ.X₀.1 :=
        le_antisymm (leOfHom ((Φ.iterationFunctorObjBotIso J).hom.1))
          (leOfHom ((Φ.iterationFunctorObjBotIso J).inv.1))
      simpa [Φ, attachmentSuccStruct] using he
  | succ j hj ih =>
      let e := Φ.iterationFunctorObjSuccIso j hj
      have he : (F.obj (Order.succ j)).1 = Order.succ (F.obj j).1 :=
        le_antisymm (leOfHom e.hom.1) (leOfHom e.inv.1)
      rw [ih] at he
      exact he
  | isSuccLimit j hj ih =>
      let cLim := (Set.principalSegIio j).cocone F
      let hcLim : IsColimit cLim := F.isColimitOfIsWellOrderContinuous j hj
      let cStage := prodCoconeFst cLim
      have hcStage : IsColimit cStage := prodCoconeFst_isColimit cLim hcLim
      have hLUB : IsLUB (Set.range
          ((Set.principalSegIio j).monotone.functor ⋙ F ⋙
            CategoryTheory.Prod.fst J (Over (Under.mk q))).obj)
          (F.obj j).1 :=
        Preorder.isLUB_of_isColimit _ hcStage
      apply le_antisymm
      · apply hLUB.2
        rintro x ⟨k, rfl⟩
        simpa [F, ih k.1 k.2] using k.2.le
      · rw [hj.le_iff_forall_le]
        intro k hk
        have hmap : (F.obj k).1 ≤ (F.obj j).1 :=
          leOfHom ((F.map (homOfLE hk.le)).1)
        simpa [F, ih k hk] using hmap

private noncomputable def attachmentTower_transfiniteComposition
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (T : MorphismProperty C) (hg : ∀ i, T (g i)) :
    T.pushouts.TransfiniteCompositionOfShape (WithTop c.ι)
      ((attachmentSuccStruct g c).ιIteration (WithTop c.ι)).2.left.right := by
  let J := WithTop c.ι
  let Φ := attachmentSuccStruct g c
  let H := factorizationCarrierFunctor q J
  let hFull := Φ.transfiniteCompositionOfShapeιIteration J
  let cFull : Cocone hFull.F := Cocone.mk _ hFull.incl
  let cCarrier := factorizationCarrierCocone cFull
  let hcCarrier : IsColimit cCarrier :=
    factorizationCarrierCocone_isColimit_of_orderBot cFull hFull.isColimit
  have hContinuous : (hFull.F ⋙ H).IsWellOrderContinuous :=
    { nonempty_isColimit := fun j hj ↦ ⟨by
        letI : OrderBot (Set.Iio j) :=
          { bot := ⟨⊥, hj.bot_lt⟩
            bot_le := fun x ↦ show (⊥ : J) ≤ x.1 from bot_le }
        let cLim := (Set.principalSegIio j).cocone hFull.F
        let hcLim : IsColimit cLim :=
          hFull.F.isColimitOfIsWellOrderContinuous j hj
        change IsColimit (factorizationCarrierCocone cLim)
        exact factorizationCarrierCocone_isColimit_of_orderBot cLim hcLim⟩ }
  refine
    { F := hFull.F ⋙ H
      isoBot := H.mapIso hFull.isoBot
      isWellOrderContinuous := hContinuous
      incl := cCarrier.ι
      isColimit := hcCarrier
      fac := by
        change H.map hFull.isoBot.inv ≫ H.map (hFull.incl.app ⊥) =
          H.map (Φ.ιIteration J)
        rw [← H.map_comp, hFull.fac]
      map_mem := fun j hj ↦ by
        have hne : j ≠ ⊤ := by
          intro h
          subst j
          exact hj isMax_top
        let k : c.ι := j.untop hne
        have hstage : ((Φ.iterationFunctor J).obj j).1 = j :=
          attachmentIteration_stage_eq g c j
        have hcell : attachmentStageCell ((Φ.iterationFunctor J).obj j).1 = some k := by
          rw [hstage]
          rw [← WithTop.coe_untop j hne]
          rfl
        have hstep : T.pushouts (H.map (Φ.toSucc ((Φ.iterationFunctor J).obj j))) :=
          attachmentSuccStruct_toSucc_carrier_mem g c T hg _ k hcell
        change T.pushouts
          (H.map ((Φ.iterationFunctor J).map (homOfLE (Order.le_succ j))))
        rw [Φ.iterationFunctor_map_succ j hj]
        have hH : H.map (Φ.toSucc ((Φ.iterationFunctor J).obj j) ≫
            (Φ.iterationFunctorObjSuccIso j hj).inv) =
            H.map (Φ.toSucc ((Φ.iterationFunctor J).obj j)) ≫
              H.map (Φ.iterationFunctorObjSuccIso j hj).inv :=
          H.map_comp _ _
        rw [hH]
        let eH := H.mapIso (Φ.iterationFunctorObjSuccIso j hj)
        let a : Arrow.mk (H.map (Φ.toSucc ((Φ.iterationFunctor J).obj j)) ≫
            H.map (Φ.iterationFunctorObjSuccIso j hj).inv) ≅
            Arrow.mk (H.map (Φ.toSucc ((Φ.iterationFunctor J).obj j))) :=
          Arrow.isoMk (Iso.refl _) eH (by
            dsimp
            rw [Category.assoc]
            have hi : H.map (Φ.iterationFunctorObjSuccIso j hj).inv ≫ eH.hom = 𝟙 _ :=
              eH.inv_hom_id
            rw [hi, Category.comp_id, Category.id_comp])
        exact (T.pushouts.arrow_mk_iso_iff a).2 hstep }

@[nolint unusedArguments]
private noncomputable def attachmentTowerCellStateToFinal
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (k : c.ι) :
    attachFactorization g c k
        ((attachmentSuccStruct g c).iterationFunctor (WithTop c.ι) |>.obj (k : WithTop c.ι)).2 ⟶
      ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2 := by
  let J := WithTop c.ι
  let Φ := attachmentSuccStruct g c
  let F := Φ.iterationFunctor J
  let j : J := k
  have hj : ¬ IsMax j := by
    rw [not_isMax_iff]
    exact ⟨⊤, WithTop.coe_lt_top k⟩
  have hstage : (F.obj j).1 = j := attachmentIteration_stage_eq g c j
  have hcell : attachmentStageCell (F.obj j).1 = some k := by
    rw [hstage]
    rfl
  have hstep := attachmentFactorizationStep_eq_of_cell g c (F.obj j) k hcell
  let eObj : (attachmentFactorizationStep g c (F.obj j)).obj =
      attachFactorization g c k (F.obj j).2 := congrArg CategoricalSuccStep.obj hstep
  let castToStep : attachFactorization g c k (F.obj j).2 ⟶
      (attachmentFactorizationStep g c (F.obj j)).obj := eqToHom eObj.symm
  exact castToStep ≫ (Φ.iterationFunctorObjSuccIso j hj).inv.2 ≫
    ((Φ.iterationCocone J).ι.app (Order.succ j)).2

private noncomputable def attachmentTowerFinalCell
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (k : c.ι) : B (c.π k) ⟶
      ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.right :=
  pushout.inl (g (c.π k))
      (cellAttachMap g c k
        ((attachmentSuccStruct g c).iterationFunctor (WithTop c.ι) |>.obj
          (k : WithTop c.ι)).2) ≫
    (attachmentTowerCellStateToFinal g c k).left.right

private theorem attachmentTowerFinalCell_target
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (k : c.ι) :
    attachmentTowerFinalCell g c k ≫
        ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.hom.right =
      cellTargetMap g c k := by
  let Φ := attachmentSuccStruct g c
  let Zk := (Φ.iterationFunctor (WithTop c.ι)).obj (k : WithTop c.ι)
  let t := attachmentTowerCellStateToFinal g c k
  have hwOver := Over.w t
  have hw : t.left.right ≫ (Φ.iteration (WithTop c.ι)).2.hom.right =
      (attachFactorization g c k Zk.2).hom.right := by
    simpa only [Under.comp_right] using congrArg Under.Hom.right hwOver
  calc
    attachmentTowerFinalCell g c k ≫
        (Φ.iteration (WithTop c.ι)).2.hom.right =
      pushout.inl (g (c.π k)) (cellAttachMap g c k Zk.2) ≫
        (t.left.right ≫ (Φ.iteration (WithTop c.ι)).2.hom.right) := by
          exact Category.assoc _ _ _
    _ = pushout.inl (g (c.π k)) (cellAttachMap g c k Zk.2) ≫
        (attachFactorization g c k Zk.2).hom.right := by
      exact congrArg (fun z ↦
        pushout.inl (g (c.π k)) (cellAttachMap g c k Zk.2) ≫ z) hw
    _ = cellTargetMap g c k := by
      change pushout.inl (g (c.π k)) (cellAttachMap g c k Zk.2) ≫
        attachToTarget g c k Zk.2 = cellTargetMap g c k
      exact pushout.inl_desc _ _ _

private theorem attachmentTowerFinalCell_boundary
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (k : c.ι) :
    g (c.π k) ≫ attachmentTowerFinalCell g c k =
      c.cofan₁.inj k ≫ c.g₁ ≫
        ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.hom := by
  let Φ := attachmentSuccStruct g c
  let Zk := (Φ.iterationFunctor (WithTop c.ι)).obj (k : WithTop c.ι)
  let t := attachmentTowerCellStateToFinal g c k
  let m : Zk.2 ⟶ (Φ.iteration (WithTop c.ι)).2 :=
    attachFactorizationMap g c k Zk.2 ≫ t
  have hw : Zk.2.left.hom ≫ m.left.right =
      (Φ.iteration (WithTop c.ι)).2.left.hom := by
    exact Under.w m.left
  calc
    g (c.π k) ≫ attachmentTowerFinalCell g c k =
      (g (c.π k) ≫
        pushout.inl (g (c.π k)) (cellAttachMap g c k Zk.2)) ≫
          t.left.right := by
            exact (Category.assoc _ _ _).symm
    _ = (cellAttachMap g c k Zk.2 ≫
        (attachFactorizationMap g c k Zk.2).left.right) ≫ t.left.right := by
      rw [pushout.condition]
      have hmap : (attachFactorizationMap g c k Zk.2).left.right =
          pushout.inr (g (c.π k)) (cellAttachMap g c k Zk.2) := rfl
      rw [hmap]
      rfl
    _ = cellAttachMap g c k Zk.2 ≫ m.left.right := by
      have hm : m.left.right =
          (attachFactorizationMap g c k Zk.2).left.right ≫ t.left.right := rfl
      rw [hm, Category.assoc]
    _ = c.cofan₁.inj k ≫ c.g₁ ≫
        (Φ.iteration (WithTop c.ι)).2.left.hom := by
      change (c.cofan₁.inj k ≫ c.g₁ ≫ Zk.2.left.hom) ≫
        m.left.right = c.cofan₁.inj k ≫ c.g₁ ≫
          (Φ.iteration (WithTop c.ι)).2.left.hom
      simp only [Category.assoc]
      rw [hw]

private noncomputable def attachmentTowerFinalCofan
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    Cofan (fun k ↦ B (c.π k)) :=
  Cofan.mk ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.right
    (attachmentTowerFinalCell g c)

private noncomputable def attachmentTowerFinalCellsMap
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    c.cofan₂.pt ⟶
      ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.right :=
  c.isColimit₂.desc (attachmentTowerFinalCofan g c)

private theorem attachmentTowerFinalCellsMap_fac
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (k : c.ι) :
    c.cofan₂.inj k ≫ attachmentTowerFinalCellsMap g c =
      attachmentTowerFinalCell g c k := by
  change c.cofan₂.inj k ≫
    c.isColimit₂.desc (attachmentTowerFinalCofan g c) =
      attachmentTowerFinalCell g c k
  exact Cofan.IsColimit.fac c.isColimit₂ (attachmentTowerFinalCell g c) k

private theorem attachmentTowerFinalCellsMap_comm
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    c.g₁ ≫ ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.hom =
      c.m ≫ attachmentTowerFinalCellsMap g c := by
  apply Cofan.IsColimit.hom_ext c.isColimit₁
  intro k
  calc
    c.cofan₁.inj k ≫ c.g₁ ≫
        ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.hom =
      g (c.π k) ≫ attachmentTowerFinalCell g c k :=
        (attachmentTowerFinalCell_boundary g c k).symm
    _ = (c.cofan₁.inj k ≫ c.m) ≫ attachmentTowerFinalCellsMap g c := by
      rw [c.hm k, Category.assoc]
      rw [attachmentTowerFinalCellsMap_fac g c k]
    _ = c.cofan₁.inj k ≫ c.m ≫ attachmentTowerFinalCellsMap g c :=
      Category.assoc _ _ _

private noncomputable def attachmentTowerFinalInverse
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    Y ⟶ ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.right :=
  c.isPushout.desc
    ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.hom
    (attachmentTowerFinalCellsMap g c)
    (attachmentTowerFinalCellsMap_comm g c)

private theorem attachmentTowerFinalInverse_hom
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    attachmentTowerFinalInverse g c ≫
        ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.hom.right = 𝟙 Y := by
  let Φ := attachmentSuccStruct g c
  let s := attachmentTowerFinalInverse g c
  let r := (Φ.iteration (WithTop c.ι)).2.hom.right
  have hsX : q ≫ s = (Φ.iteration (WithTop c.ι)).2.left.hom := by
    dsimp [s, attachmentTowerFinalInverse]
    exact c.isPushout.inl_desc _ _ _
  have hsB : c.g₂ ≫ s = attachmentTowerFinalCellsMap g c := by
    dsimp [s, attachmentTowerFinalInverse]
    exact c.isPushout.inr_desc _ _ _
  apply c.isPushout.hom_ext
  · rw [← Category.assoc, hsX]
    have hqr : (Φ.iteration (WithTop c.ι)).2.left.hom ≫ r = q :=
      Under.w (Φ.iteration (WithTop c.ι)).2.hom
    rw [hqr, Category.comp_id]
  · rw [← Category.assoc, hsB]
    apply Cofan.IsColimit.hom_ext c.isColimit₂
    intro k
    calc
      c.cofan₂.inj k ≫ attachmentTowerFinalCellsMap g c ≫ r =
        attachmentTowerFinalCell g c k ≫ r := by
          rw [← Category.assoc, attachmentTowerFinalCellsMap_fac g c k]
      _ = cellTargetMap g c k := attachmentTowerFinalCell_target g c k
      _ = c.cofan₂.inj k ≫ c.g₂ := rfl
      _ = c.cofan₂.inj k ≫ c.g₂ ≫ 𝟙 Y := by rw [Category.comp_id]

private noncomputable def attachmentTowerFinalSection
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    terminalFactorization q ⟶
      ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2 := by
  let Φ := attachmentSuccStruct g c
  let s := attachmentTowerFinalInverse g c
  let u : (Under.mk q : Under X) ⟶ (Φ.iteration (WithTop c.ι)).2.left :=
    Under.homMk s (by
      dsimp [s, attachmentTowerFinalInverse]
      exact c.isPushout.inl_desc _ _ _)
  exact Over.homMk u (by
    apply Under.UnderMorphism.ext
    change s ≫ (Φ.iteration (WithTop c.ι)).2.hom.right = 𝟙 Y
    exact attachmentTowerFinalInverse_hom g c)

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentTower_incl_eq_toTerminal_section
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))]
    (j : WithTop c.ι) :
    factorizationToTerminal
        (((attachmentSuccStruct g c).iterationFunctor (WithTop c.ι)).obj j).2 ≫
        attachmentTowerFinalSection g c =
      iterationSndIncl (WithTop c.ι) (attachmentSuccStruct g c) j := by
  let J := WithTop c.ι
  let Φ := attachmentSuccStruct g c
  let sec : terminalFactorization q ⟶ (Φ.iteration J).2 :=
    attachmentTowerFinalSection g c
  change factorizationToTerminal ((Φ.iterationFunctor J).obj j).2 ≫
      sec =
    iterationSndIncl J Φ j
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      obtain rfl := hj.eq_bot
      let eD := prodIsoSnd (Φ.iterationFunctorObjBotIso J)
      rw [← cancel_epi eD.inv]
      exact initialFactorization_hom_ext _ _
  | succ j hj ih =>
      have hne : j ≠ ⊤ := by
        intro h
        subst j
        exact hj isMax_top
      obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
      let Zj : WithTop c.ι × Over (Under.mk q) :=
        (Φ.iterationFunctor J).obj (k : WithTop c.ι)
      let eD : ((Φ.iterationFunctor J).obj (Order.succ (k : WithTop c.ι))).2 ≅
          (Φ.succ ((Φ.iterationFunctor J).obj (k : WithTop c.ι))).2 :=
        prodIsoSnd (Φ.iterationFunctorObjSuccIso (k : WithTop c.ι) hj)
      have hstage : Zj.1 = (k : WithTop c.ι) :=
        attachmentIteration_stage_eq g c (k : WithTop c.ι)
      have hcell : attachmentStageCell Zj.1 = some k := by
        rw [hstage]
        rfl
      have hObj : (attachmentFactorizationStep g c Zj).obj =
          attachFactorization g c k Zj.2 :=
        attachmentFactorizationStep_obj_eq_of_cell g c Zj k hcell
      let eStep : (attachmentFactorizationStep g c Zj).obj ≅
          attachFactorization g c k Zj.2 := eqToIso hObj
      let eAttach : ((Φ.iterationFunctor J).obj (Order.succ (k : WithTop c.ι))).2 ≅
          attachFactorization g c k Zj.2 := eD ≪≫ eStep
      rw [← cancel_epi eAttach.inv]
      let leftD : attachFactorization g c k Zj.2 ⟶ terminalFactorization q :=
        eAttach.inv ≫ factorizationToTerminal
          ((Φ.iterationFunctor J).obj (Order.succ (k : WithTop c.ι))).2
      have hleftD : leftD = factorizationToTerminal (attachFactorization g c k Zj.2) := by
        exact factorizationToTerminal_natural eAttach.inv
      have hleftComp :
          (eAttach.inv ≫ factorizationToTerminal ((Φ.iterationFunctor J).obj
            (Order.succ (k : WithTop c.ι))).2) ≫ sec =
            factorizationToTerminal (attachFactorization g c k Zj.2) ≫ sec :=
        congrArg (fun z ↦ z ≫ sec) hleftD
      have hleftCompR :
          eAttach.inv ≫ (factorizationToTerminal ((Φ.iterationFunctor J).obj
            (Order.succ (k : WithTop c.ι))).2 ≫ sec) =
            factorizationToTerminal (attachFactorization g c k Zj.2) ≫ sec :=
        (Category.assoc _ _ _).symm.trans hleftComp
      apply Over.OverMorphism.ext
      apply Under.UnderMorphism.ext
      apply (attachFactorizationMap_isPushout g c k Zj.2).hom_ext
      · have hcellS : cellTargetMap g c k ≫ attachmentTowerFinalInverse g c =
            attachmentTowerFinalCell g c k := by
          change (c.cofan₂.inj k ≫ c.g₂) ≫ attachmentTowerFinalInverse g c =
            attachmentTowerFinalCell g c k
          calc
            (c.cofan₂.inj k ≫ c.g₂) ≫ attachmentTowerFinalInverse g c =
              c.cofan₂.inj k ≫ attachmentTowerFinalCellsMap g c := by
              rw [Category.assoc]
              congr 1
              dsimp [attachmentTowerFinalInverse]
              exact c.isPushout.inr_desc _ _ _
            _ = attachmentTowerFinalCell g c k :=
              attachmentTowerFinalCellsMap_fac g c k
        rw [hleftCompR]
        have ht : eAttach.inv ≫ iterationSndIncl J Φ (Order.succ (k : WithTop c.ι)) =
            attachmentTowerCellStateToFinal g c k := by
          apply Over.OverMorphism.ext
          apply Under.UnderMorphism.ext
          dsimp [eAttach, eD, eStep, attachmentTowerCellStateToFinal]
          exact Category.assoc _ _ _
        have hcellCarrier :
            pushout.inl (g (c.π k)) (cellAttachMap g c k Zj.2) ≫
                (factorizationToTerminal (attachFactorization g c k Zj.2) ≫ sec).left.right =
              attachmentTowerFinalCell g c k := by
          change pushout.inl (g (c.π k)) (cellAttachMap g c k Zj.2) ≫
              (attachToTarget g c k Zj.2 ≫ attachmentTowerFinalInverse g c) =
            attachmentTowerFinalCell g c k
          unfold attachToTarget
          rw [← Category.assoc, pushout.inl_desc]
          exact hcellS
        have hfinalDef : attachmentTowerFinalCell g c k =
            pushout.inl (g (c.π k)) (cellAttachMap g c k Zj.2) ≫
              (attachmentTowerCellStateToFinal g c k).left.right := rfl
        rw [ht]
        exact hcellCarrier.trans hfinalDef
      · let oldD : Zj.2 ⟶ (Φ.iteration J).2 :=
          attachFactorizationMap g c k Zj.2 ≫ eAttach.inv ≫
            iterationSndIncl J Φ (Order.succ (k : WithTop c.ι))
        have hmap := Φ.iterationFunctor_map_succ (k : WithTop c.ι) hj
        have hstepMap : attachFactorizationMap g c k Zj.2 ≫ eStep.inv =
            (attachmentFactorizationStep g c Zj).map := by
          exact attachmentFactorizationStep_map_eq_of_cell g c Zj k hcell
        have heAttachInv : eAttach.inv = eStep.inv ≫ eD.inv := rfl
        have htoSucc : attachFactorizationMap g c k Zj.2 ≫ eAttach.inv =
            ((Φ.iterationFunctor J).map
              (homOfLE (Order.le_succ (k : WithTop c.ι)) :
                (k : WithTop c.ι) ⟶ Order.succ (k : WithTop c.ι))).2 := by
          calc
            attachFactorizationMap g c k Zj.2 ≫ eAttach.inv =
                (attachFactorizationMap g c k Zj.2 ≫ eStep.inv) ≫ eD.inv := by
              rw [heAttachInv]
              exact (Category.assoc _ _ _).symm
            _ = (attachmentFactorizationStep g c Zj).map ≫ eD.inv := by
              rw [hstepMap]
            _ = ((Φ.iterationFunctor J).map
                (homOfLE (Order.le_succ (k : WithTop c.ι)) :
                  (k : WithTop c.ι) ⟶ Order.succ (k : WithTop c.ι))).2 := by
              have hmapD := congrArg Prod.snd hmap
              change ((Φ.iterationFunctor J).map
                (homOfLE (Order.le_succ (k : WithTop c.ι)) :
                  (k : WithTop c.ι) ⟶ Order.succ (k : WithTop c.ι))).2 =
                  (attachmentFactorizationStep g c Zj).map ≫ eD.inv at hmapD
              exact hmapD.symm
        have holdD : oldD = iterationSndIncl J Φ (k : WithTop c.ι) := by
          dsimp [oldD]
          rw [← Category.assoc, htoSucc]
          exact iterationSndIncl_naturality J Φ
            (homOfLE (Order.le_succ (k : WithTop c.ι)) :
              (k : WithTop c.ι) ⟶ Order.succ (k : WithTop c.ι))
        have hLeft : attachFactorizationMap g c k Zj.2 ≫
            (factorizationToTerminal (attachFactorization g c k Zj.2) ≫ sec) =
              iterationSndIncl J Φ (k : WithTop c.ι) := by
          rw [← Category.assoc, factorizationToTerminal_natural, ih]
        have hLeftOrig : attachFactorizationMap g c k Zj.2 ≫
            (eAttach.inv ≫ (factorizationToTerminal
              ((Φ.iterationFunctor J).obj (Order.succ (k : WithTop c.ι))).2 ≫ sec)) =
              iterationSndIncl J Φ (k : WithTop c.ι) := by
          calc
            attachFactorizationMap g c k Zj.2 ≫
                (eAttach.inv ≫ (factorizationToTerminal
                  ((Φ.iterationFunctor J).obj (Order.succ (k : WithTop c.ι))).2 ≫ sec)) =
              attachFactorizationMap g c k Zj.2 ≫
                (factorizationToTerminal (attachFactorization g c k Zj.2) ≫ sec) := by
              exact congrArg (fun z ↦ attachFactorizationMap g c k Zj.2 ≫ z) hleftCompR
            _ = iterationSndIncl J Φ (k : WithTop c.ι) := hLeft
        have hRight : attachFactorizationMap g c k Zj.2 ≫
            (eAttach.inv ≫ iterationSndIncl J Φ (Order.succ (k : WithTop c.ι))) =
              iterationSndIncl J Φ (k : WithTop c.ι) := by
          calc
            attachFactorizationMap g c k Zj.2 ≫
                (eAttach.inv ≫ iterationSndIncl J Φ (Order.succ (k : WithTop c.ι))) =
              (attachFactorizationMap g c k Zj.2 ≫ eAttach.inv) ≫
                iterationSndIncl J Φ (Order.succ (k : WithTop c.ι)) :=
              (Category.assoc _ _ _).symm
            _ = iterationSndIncl J Φ (k : WithTop c.ι) := by
              dsimp [oldD] at holdD
              exact (Category.assoc _ _ _).trans holdD
        simpa only [Over.comp_left, Under.comp_right] using
          congrArg (fun z ↦ z.left.right) (hLeftOrig.trans hRight.symm)
  | isSuccLimit j hj ih =>
      let cLim := (Set.principalSegIio j).cocone (Φ.iterationFunctor J)
      let hcLim : IsColimit cLim :=
        (Φ.iterationFunctor J).isColimitOfIsWellOrderContinuous j hj
      let cD := prodCoconeSnd cLim
      let hcD : IsColimit cD := prodCoconeSnd_isColimit cLim hcLim
      apply hcD.hom_ext
      rintro ⟨k, hk⟩
      let fk := ((Φ.iterationFunctor J).map (homOfLE hk.le : k ⟶ j)).2
      have hterm : fk ≫ factorizationToTerminal ((Φ.iterationFunctor J).obj j).2 =
          factorizationToTerminal ((Φ.iterationFunctor J).obj k).2 :=
        factorizationToTerminal_natural fk
      have hcocD : fk ≫ iterationSndIncl J Φ j =
          iterationSndIncl J Φ k := by
        exact iterationSndIncl_naturality J Φ (homOfLE hk.le : k ⟶ j)
      calc
        fk ≫ (factorizationToTerminal ((Φ.iterationFunctor J).obj j).2 ≫
            sec) =
            (fk ≫ factorizationToTerminal ((Φ.iterationFunctor J).obj j).2) ≫
              sec :=
          (Category.assoc _ _ _).symm
        _ = factorizationToTerminal ((Φ.iterationFunctor J).obj k).2 ≫
            sec := by rw [hterm]
        _ = iterationSndIncl J Φ k := ih k hk
        _ = fk ≫ iterationSndIncl J Φ j := hcocD.symm

set_option backward.isDefEq.respectTransparency false in
private theorem attachmentTowerFinal_hom_inverse
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.hom.right ≫
        attachmentTowerFinalInverse g c =
      𝟙 ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.right := by
  let J := WithTop c.ι
  let Φ := attachmentSuccStruct g c
  let cFull : Cocone (Φ.iterationFunctor J) := Φ.iterationCocone J
  let cCarrier := factorizationCarrierCocone cFull
  let hcCarrier : IsColimit cCarrier :=
    factorizationCarrierCocone_isColimit_of_orderBot cFull
      (Φ.isColimitIterationCocone J)
  let r := (Φ.iteration J).2.hom.right
  let s := attachmentTowerFinalInverse g c
  apply hcCarrier.hom_ext
  intro j
  let d := iterationSndIncl J Φ j
  have hdr : d.left.right ≫ r = ((Φ.iterationFunctor J).obj j).2.hom.right := by
    have hd := Over.w d
    simpa only [Under.comp_right] using congrArg Under.Hom.right hd
  have hds : ((Φ.iterationFunctor J).obj j).2.hom.right ≫ s = d.left.right := by
    exact congrArg (fun z ↦ z.left.right)
      (attachmentTower_incl_eq_toTerminal_section g c j)
  change d.left.right ≫ (r ≫ s) = d.left.right ≫ 𝟙 _
  rw [← Category.assoc, hdr, hds, Category.comp_id]

private noncomputable def attachmentTowerTargetIso
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.left.right ≅ Y where
  hom := ((attachmentSuccStruct g c).iteration (WithTop c.ι)).2.hom.right
  inv := attachmentTowerFinalInverse g c
  hom_inv_id := attachmentTowerFinal_hom_inverse g c
  inv_hom_id := attachmentTowerFinalInverse_hom g c

private theorem attachmentTowerComposite_targetIso
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [LinearOrder c.ι] [OrderBot c.ι]
    [SuccOrder (WithTop c.ι)] [WellFoundedLT (WithTop c.ι)]
    [HasIterationOfShape (WithTop c.ι)
      (WithTop c.ι × Over (Under.mk q))] :
    ((attachmentSuccStruct g c).ιIteration (WithTop c.ι)).2.left.right ≫
        (attachmentTowerTargetIso g c).hom = q := by
  let J := WithTop c.ι
  let Φ := attachmentSuccStruct g c
  let a := (Φ.ιIteration J).2
  have ha : a.left.right = (Φ.iteration J).2.left.hom := by
    have h := Under.w a.left
    change (𝟙 X) ≫ a.left.right = (Φ.iteration J).2.left.hom at h
    exact (Category.id_comp _).symm.trans h
  change a.left.right ≫ (Φ.iteration J).2.hom.right = q
  rw [ha]
  exact Under.w (Φ.iteration J).2.hom

private theorem attachCells_empty_isIso
    {C : Type u₁} [Category.{v₁} C]
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    [IsEmpty c.ι] : IsIso q := by
  let r : c.cofan₂.pt ⟶ c.cofan₁.pt :=
    c.isColimit₂.desc (Cofan.mk c.cofan₁.pt (fun k ↦ isEmptyElim k))
  have hmr : c.m ≫ r = 𝟙 c.cofan₁.pt := by
    apply Cofan.IsColimit.hom_ext c.isColimit₁
    intro k
    exact isEmptyElim k
  have hrm : r ≫ c.m = 𝟙 c.cofan₂.pt := by
    apply Cofan.IsColimit.hom_ext c.isColimit₂
    intro k
    exact isEmptyElim k
  let instM : IsIso c.m := ⟨⟨r, hmr, hrm⟩⟩
  exact c.isPushout.isIso_inl_of_isIso (inst := instM)

private theorem attachCells_mem_transfinitePushouts
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C]
    (T : MorphismProperty C)
    {ι : Type u} {A B : ι → C} (g : (i : ι) → A i ⟶ B i)
    {X Y : C} {q : X ⟶ Y} (c : AttachCells.{u} g q)
    (hg : ∀ i, T (g i)) : transfiniteCompositions.{u} T.pushouts q := by
  classical
  cases isEmpty_or_nonempty c.ι with
  | inl hEmpty =>
      let _ : IsEmpty c.ι := hEmpty
      let iq : IsIso q := attachCells_empty_isIso g c
      let e : Arrow.mk (𝟙 X) ≅ Arrow.mk q :=
        Arrow.isoMk (Iso.refl X) (@asIso _ _ _ _ q iq) (by simp)
      let hFin : T.pushouts.TransfiniteCompositionOfShape (Fin 1) q :=
        (MorphismProperty.TransfiniteCompositionOfShape.id T.pushouts X).ofArrowIso e
      let _ : SuccOrder (ULift.{u} (Fin 1)) := SuccOrder.ofLinearWellFoundedLT _
      let hLift : T.pushouts.TransfiniteCompositionOfShape (ULift.{u} (Fin 1)) q :=
        hFin.ofOrderIso ULift.orderIso
      exact transfiniteCompositionsOfShape_le_transfiniteCompositions
        T.pushouts (ULift.{u} (Fin 1)) q hLift.mem
  | inr hNonempty =>
      let _ : Nonempty c.ι := hNonempty
      let _ : LinearOrder c.ι := WellOrderingRel.isWellOrder.linearOrder
      let _ : WellFoundedLT c.ι := WellOrderingRel.isWellOrder.wf
      let _ : OrderBot c.ι := WellFoundedLT.toOrderBot c.ι
      let J := WithTop c.ι
      let D := Over (Under.mk q)
      let _ : SuccOrder J := SuccOrder.ofLinearWellFoundedLT _
      let _ : HasIterationOfShape J (J × D) :=
        { hasColimitsOfShape := by
            let _ : HasColimitsOfShape J J :=
              hasColimitsOfShapeWellFoundedOrderTop J J
            let _ : HasColimitsOfShape J D := inferInstance
            exact hasColimitsOfShapeProd J
          hasColimitsOfShape_of_isSuccLimit := fun j hj ↦ by
            let _ : HasColimitsOfShape (Set.Iio j) J :=
              hasColimitsOfShapeWellFoundedOrderTop (Set.Iio j) J
            let _ : HasColimitsOfShape (Set.Iio j) D := inferInstance
            exact hasColimitsOfShapeProd (Set.Iio j) }
      let hTower := attachmentTower_transfiniteComposition g c T hg
      let eTarget := attachmentTowerTargetIso g c
      let eArrow : Arrow.mk
          ((attachmentSuccStruct g c).ιIteration J).2.left.right ≅ Arrow.mk q :=
        Arrow.isoMk (Iso.refl X) eTarget
          ((Category.id_comp q).trans (attachmentTowerComposite_targetIso g c).symm)
      let hTarget : T.pushouts.TransfiniteCompositionOfShape J q :=
        hTower.ofArrowIso eArrow
      exact transfiniteCompositionsOfShape_le_transfiniteCompositions
        T.pushouts J q hTarget.mem

private theorem pushedCoproducts_le_transfinitePushouts
    {C : Type u₁} [Category.{v₁} C] [HasPushouts C]
    [HasColimitsOfSize.{u, u} C] (T : MorphismProperty C) :
    (coproducts.{u} T).pushouts ≤ transfiniteCompositions.{u} T.pushouts := by
  intro X Y q hq
  rcases hq with ⟨P, Q, p, f, g₂, hp, sq⟩
  rw [coproducts_iff] at hp
  rcases hp with ⟨κ, ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩⟩
  let A : κ → C := fun k ↦ F₁.obj ⟨k⟩
  let B : κ → C := fun k ↦ F₂.obj ⟨k⟩
  let cell : (k : κ) → A k ⟶ B k := fun k ↦ φ.app ⟨k⟩
  let e₁ : F₁ ≅ Discrete.functor A := Discrete.natIsoFunctor
  let e₂ : F₂ ≅ Discrete.functor B := Discrete.natIsoFunctor
  let cf₁ : Cofan A :=
    Cofan.mk c₁.pt (fun k ↦ (e₁.app ⟨k⟩).inv ≫ c₁.ι.app ⟨k⟩)
  let cf₂ : Cofan B :=
    Cofan.mk c₂.pt (fun k ↦ (e₂.app ⟨k⟩).inv ≫ c₂.ι.app ⟨k⟩)
  have hcf₁ : IsColimit cf₁ :=
    (IsColimit.precomposeHomEquiv e₁ _).1
      (IsColimit.ofIsoColimit h₁ (Cocone.ext (Iso.refl _)
        (by
          intro k
          exact (Category.comp_id (c₁.ι.app k)).trans
            ((e₁.app k).hom_inv_id_assoc (c₁.ι.app k)).symm)))
  have hcf₂ : IsColimit cf₂ :=
    (IsColimit.precomposeHomEquiv e₂ _).1
      (IsColimit.ofIsoColimit h₂ (Cocone.ext (Iso.refl _)
        (by
          intro k
          exact (Category.comp_id (c₂.ι.app k)).trans
            ((e₂.app k).hom_inv_id_assoc (c₂.ι.app k)).symm)))
  let ac : AttachCells.{u} cell q :=
    { ι := κ
      π := id
      cofan₁ := cf₁
      cofan₂ := cf₂
      isColimit₁ := hcf₁
      isColimit₂ := hcf₂
      m := h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι))
      hm := fun k ↦ by
        dsimp [cell, A, B, cf₁, cf₂, e₁, e₂]
        simp [Discrete.natIsoFunctor, h₁.fac]
      g₁ := f
      g₂ := g₂
      isPushout := sq }
  exact attachCells_mem_transfinitePushouts T cell ac (fun k ↦ hφ ⟨k⟩)

private theorem boundaryPushedCoproducts_le_transfiniteBoundaryPushouts :
    (coproducts.{u} (I.{u} : MorphismProperty TopCat.{u})).pushouts ≤
      transfiniteCompositions.{u} (I.{u} : MorphismProperty TopCat.{u}).pushouts :=
  pushedCoproducts_le_transfinitePushouts (I.{u} : MorphismProperty TopCat.{u})

private structure RelativeCellCobaseLadder
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B}
    {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y) where
  outerPushout : IsPushout i f f' j
  G : J ⥤ TopCat.{u}
  comparison : hT.F ⟶ G
  isoBot : G.obj ⊥ ≅ X
  bottomComparison : hT.isoBot.inv ≫ comparison.app ⊥ ≫ isoBot.hom = f
  isWellOrderContinuous : G.IsWellOrderContinuous
  successorPushout (k : J) (hk : ¬ IsMax k) :
    IsPushout (hT.F.map (homOfLE (Order.le_succ k)))
      (comparison.app k) (comparison.app (Order.succ k))
      (G.map (homOfLE (Order.le_succ k)))
  incl : G ⟶ (Functor.const J).obj Y
  isColimit : IsColimit (Cocone.mk Y incl)
  comparison_fac : hT.incl ≫ (Functor.const J).map f' = comparison ≫ incl

private theorem RelativeCellCobaseLadder.colimitComparison_eq
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    {hT : R.TransfiniteCompositionOfShape J i} {f : A ⟶ X} {f' : B ⟶ Y}
    {j : X ⟶ Y} (L : RelativeCellCobaseLadder hT f f' j) :
    hT.isColimit.desc (Cocone.mk Y (L.comparison ≫ L.incl)) = f' := by
  apply hT.isColimit.hom_ext
  intro k
  rw [hT.isColimit.fac]
  exact (NatTrans.congr_app L.comparison_fac k).symm

private noncomputable def ladderBottomMap
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) :
    hT.F.obj ⊥ ⟶ X := hT.isoBot.hom ≫ f

private noncomputable def ladderBottomToStage
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (k : J) :
    hT.F.obj ⊥ ⟶ hT.F.obj k := hT.F.map (homOfLE bot_le)

private noncomputable abbrev ladderObj
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) (k : J) : TopCat.{u} :=
  pushout (ladderBottomToStage hT k) (ladderBottomMap hT f)

private noncomputable abbrev ladderComparison
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) (k : J) :
    hT.F.obj k ⟶ ladderObj hT f k :=
  pushout.inl (ladderBottomToStage hT k) (ladderBottomMap hT f)

private noncomputable abbrev ladderBaseLeg
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) (k : J) :
    X ⟶ ladderObj hT f k :=
  pushout.inr (ladderBottomToStage hT k) (ladderBottomMap hT f)

private noncomputable def ladderTransition
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X)
    {k l : J} (a : k ⟶ l) : ladderObj hT f k ⟶ ladderObj hT f l :=
  (IsPushout.of_hasPushout (ladderBottomToStage hT k) (ladderBottomMap hT f)).desc
    (hT.F.map a ≫ ladderComparison hT f l) (ladderBaseLeg hT f l) (by
      have hmap : ladderBottomToStage hT k ≫ hT.F.map a =
          ladderBottomToStage hT l := by
        dsimp [ladderBottomToStage]
        rw [← hT.F.map_comp]
        exact congrArg hT.F.map (Subsingleton.elim _ _)
      rw [← Category.assoc, hmap]
      exact pushout.condition)

@[reassoc]
private theorem ladderComparison_transition
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X)
    {k l : J} (a : k ⟶ l) :
    ladderComparison hT f k ≫ ladderTransition hT f a =
      hT.F.map a ≫ ladderComparison hT f l :=
  (IsPushout.of_hasPushout (ladderBottomToStage hT k)
    (ladderBottomMap hT f)).inl_desc _ _ _

@[reassoc]
private theorem ladderBaseLeg_transition
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X)
    {k l : J} (a : k ⟶ l) :
    ladderBaseLeg hT f k ≫ ladderTransition hT f a = ladderBaseLeg hT f l :=
  (IsPushout.of_hasPushout (ladderBottomToStage hT k)
    (ladderBottomMap hT f)).inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev ladderFunctor
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) : J ⥤ TopCat.{u} where
  obj k := ladderObj hT f k
  map a := ladderTransition hT f a
  map_id k := by
    apply (IsPushout.of_hasPushout (ladderBottomToStage hT k) (ladderBottomMap hT f)).hom_ext
    · rw [ladderComparison_transition, hT.F.map_id, Category.id_comp,
        Category.comp_id]
    · rw [ladderBaseLeg_transition, Category.comp_id]
  map_comp a b := by
    apply (IsPushout.of_hasPushout (ladderBottomToStage hT _) (ladderBottomMap hT f)).hom_ext
    · rw [ladderComparison_transition, ladderComparison_transition_assoc,
        ladderComparison_transition, hT.F.map_comp]
      exact Category.assoc _ _ _
    · rw [ladderBaseLeg_transition, ladderBaseLeg_transition_assoc,
        ladderBaseLeg_transition]

private noncomputable def ladderComparisonNat
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) :
    hT.F ⟶ ladderFunctor hT f where
  app k := ladderComparison hT f k
  naturality _ _ a := (ladderComparison_transition hT f a).symm

private theorem ladderBottomPushout
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) :
    IsPushout (ladderBottomToStage hT ⊥) (ladderBottomMap hT f)
      (ladderBottomMap hT f) (𝟙 X) := by
  have hu : ladderBottomToStage hT ⊥ = 𝟙 (hT.F.obj ⊥) := by
    dsimp [ladderBottomToStage]
    rw [hT.F.map_id]
  rw [hu]
  exact IsPushout.of_id_fst

private noncomputable def ladderIsoBot
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) :
    (ladderFunctor hT f).obj ⊥ ≅ X :=
  (IsPushout.of_hasPushout (ladderBottomToStage hT ⊥)
    (ladderBottomMap hT f)).isoIsPushout _ _ (ladderBottomPushout hT f)

set_option backward.isDefEq.respectTransparency false in
private theorem ladder_bottomComparison
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) :
    hT.isoBot.inv ≫ (ladderComparisonNat hT f).app ⊥ ≫
        (ladderIsoBot hT f).hom = f := by
  have hcomp := (IsPushout.of_hasPushout (ladderBottomToStage hT ⊥)
    (ladderBottomMap hT f)).inl_isoIsPushout_hom _ _ (ladderBottomPushout hT f)
  have hcomp' : ladderComparison hT f ⊥ ≫ (ladderIsoBot hT f).hom =
      ladderBottomMap hT f := hcomp
  calc
    hT.isoBot.inv ≫ ladderComparison hT f ⊥ ≫
        (ladderIsoBot hT f).hom =
      hT.isoBot.inv ≫ (ladderComparison hT f ⊥ ≫
        (ladderIsoBot hT f).hom) := rfl
    _ = hT.isoBot.inv ≫ ladderBottomMap hT f := by rw [hcomp']
    _ = f := by simp [ladderBottomMap]

private theorem ladder_successorPushout
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X)
    (k : J) (_hk : ¬ IsMax k) :
    IsPushout (hT.F.map (homOfLE (Order.le_succ k)))
      ((ladderComparisonNat hT f).app k)
      ((ladderComparisonNat hT f).app (Order.succ k))
      ((ladderFunctor hT f).map (homOfLE (Order.le_succ k))) := by
  let a : k ⟶ Order.succ k := homOfLE (Order.le_succ k)
  let sqK := IsPushout.of_hasPushout (ladderBottomToStage hT k) (ladderBottomMap hT f)
  let sqS := IsPushout.of_hasPushout (ladderBottomToStage hT (Order.succ k))
    (ladderBottomMap hT f)
  have hu : ladderBottomToStage hT k ≫ hT.F.map a =
      ladderBottomToStage hT (Order.succ k) := by
    dsimp [ladderBottomToStage]
    rw [← hT.F.map_comp]
    exact congrArg hT.F.map (Subsingleton.elim _ _)
  have hb : ladderBaseLeg hT f k ≫ ladderTransition hT f a =
      ladderBaseLeg hT f (Order.succ k) := ladderBaseLeg_transition hT f a
  have outer : IsPushout (ladderBottomToStage hT k ≫ hT.F.map a)
      (ladderBottomMap hT f) (ladderComparison hT f (Order.succ k))
      (ladderBaseLeg hT f k ≫ ladderTransition hT f a) := by
    simpa only [hu, hb] using sqS
  exact outer.of_left (ladderComparison_transition hT f a).symm sqK

set_option backward.isDefEq.respectTransparency false in
private theorem ladder_isWellOrderContinuous
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) (f : A ⟶ X) :
    (ladderFunctor hT f).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    let k₀ : Set.Iio m := ⟨⊥, hm.bot_lt⟩
    let cF := (Set.principalSegIio m).cocone hT.F
    let hcF : IsColimit cF := hT.F.isColimitOfIsWellOrderContinuous m hm
    let cG := (Set.principalSegIio m).cocone (ladderFunctor hT f)
    let sqM := IsPushout.of_hasPushout (ladderBottomToStage hT m) (ladderBottomMap hT f)
    let sourceCocone (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙
        ladderFunctor hT f)) :
        Cocone ((Set.principalSegIio m).monotone.functor ⋙ hT.F) :=
      { pt := s.pt
        ι :=
          { app := fun k ↦ ladderComparison hT f k.1 ≫ s.ι.app k
            naturality := fun k l a ↦ by
              let aJ : k.1 ⟶ l.1 := (Set.principalSegIio m).monotone.functor.map a
              have hc := ladderComparison_transition hT f aJ
              have hs := s.w a
              change ladderTransition hT f aJ ≫ s.ι.app l = s.ι.app k at hs
              change hT.F.map aJ ≫ ladderComparison hT f l.1 ≫ s.ι.app l =
                (ladderComparison hT f k.1 ≫ s.ι.app k) ≫ 𝟙 s.pt
              calc
                hT.F.map aJ ≫ ladderComparison hT f l.1 ≫ s.ι.app l =
                    (hT.F.map aJ ≫ ladderComparison hT f l.1) ≫ s.ι.app l :=
                  (Category.assoc _ _ _).symm
                _ =
                    (ladderComparison hT f k.1 ≫ ladderTransition hT f aJ) ≫
                      s.ι.app l := by rw [hc]
                _ = ladderComparison hT f k.1 ≫
                    (ladderTransition hT f aJ ≫ s.ι.app l) :=
                  Category.assoc _ _ _
                _ = ladderComparison hT f k.1 ≫ s.ι.app k := by
                  rw [hs]
                _ = (ladderComparison hT f k.1 ≫ s.ι.app k) ≫ 𝟙 s.pt :=
                  (Category.comp_id _).symm } }
    let sourceDesc (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙
        ladderFunctor hT f)) : hT.F.obj m ⟶ s.pt :=
      hcF.desc (sourceCocone s)
    let baseDesc (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙
        ladderFunctor hT f)) : X ⟶ s.pt :=
      ladderBaseLeg hT f ⊥ ≫ s.ι.app k₀
    have hBottomComparison : ladderComparison hT f ⊥ =
        ladderBottomMap hT f ≫ ladderBaseLeg hT f ⊥ := by
      have hu : ladderBottomToStage hT ⊥ = 𝟙 (hT.F.obj ⊥) := by
        dsimp [ladderBottomToStage]
        rw [hT.F.map_id]
      calc
        ladderComparison hT f ⊥ = 𝟙 (hT.F.obj ⊥) ≫
            ladderComparison hT f ⊥ := (Category.id_comp _).symm
        _ = ladderBottomToStage hT ⊥ ≫ ladderComparison hT f ⊥ :=
          congrArg (fun z ↦ z ≫ ladderComparison hT f ⊥) hu.symm
        _ = ladderBottomMap hT f ≫ ladderBaseLeg hT f ⊥ := pushout.condition
    have compat (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙
        ladderFunctor hT f)) :
        ladderBottomToStage hT m ≫ sourceDesc s = ladderBottomMap hT f ≫ baseDesc s := by
      have hfac := hcF.fac (sourceCocone s) k₀
      change ladderBottomToStage hT m ≫ sourceDesc s =
        ladderComparison hT f ⊥ ≫ s.ι.app k₀ at hfac
      rw [hfac, hBottomComparison, Category.assoc]
    refine
      { desc := fun s ↦ sqM.desc (sourceDesc s) (baseDesc s) (compat s)
        fac := fun s k ↦ by
          let a : k.1 ⟶ m := homOfLE k.2.le
          let b : k₀ ⟶ k := homOfLE bot_le
          have hFfac := hcF.fac (sourceCocone s) k
          change hT.F.map a ≫ sourceDesc s =
            ladderComparison hT f k.1 ≫ s.ι.app k at hFfac
          apply (IsPushout.of_hasPushout (ladderBottomToStage hT k.1)
            (ladderBottomMap hT f)).hom_ext
          · change ladderComparison hT f k.1 ≫
              (ladderTransition hT f a ≫ sqM.desc (sourceDesc s) (baseDesc s) (compat s)) =
                ladderComparison hT f k.1 ≫ s.ι.app k
            calc
              ladderComparison hT f k.1 ≫
                  (ladderTransition hT f a ≫ sqM.desc (sourceDesc s) (baseDesc s) (compat s)) =
                (ladderComparison hT f k.1 ≫ ladderTransition hT f a) ≫
                  sqM.desc (sourceDesc s) (baseDesc s) (compat s) :=
                (Category.assoc _ _ _).symm
              _ = (hT.F.map a ≫ ladderComparison hT f m) ≫
                  sqM.desc (sourceDesc s) (baseDesc s) (compat s) := by
                rw [ladderComparison_transition]
              _ = hT.F.map a ≫
                  (ladderComparison hT f m ≫
                    sqM.desc (sourceDesc s) (baseDesc s) (compat s)) :=
                Category.assoc _ _ _
              _ = hT.F.map a ≫ sourceDesc s := by rw [sqM.inl_desc]
              _ = ladderComparison hT f k.1 ≫ s.ι.app k := hFfac
          · have hs := s.w b
            change ladderTransition hT f b ≫ s.ι.app k = s.ι.app k₀ at hs
            change ladderBaseLeg hT f k.1 ≫
              (ladderTransition hT f a ≫ sqM.desc (sourceDesc s) (baseDesc s) (compat s)) =
                ladderBaseLeg hT f k.1 ≫ s.ι.app k
            calc
              ladderBaseLeg hT f k.1 ≫
                  (ladderTransition hT f a ≫ sqM.desc (sourceDesc s) (baseDesc s) (compat s)) =
                (ladderBaseLeg hT f k.1 ≫ ladderTransition hT f a) ≫
                  sqM.desc (sourceDesc s) (baseDesc s) (compat s) :=
                (Category.assoc _ _ _).symm
              _ = ladderBaseLeg hT f m ≫
                  sqM.desc (sourceDesc s) (baseDesc s) (compat s) := by
                rw [ladderBaseLeg_transition]
              _ = baseDesc s := sqM.inr_desc _ _ _
              _ = ladderBaseLeg hT f ⊥ ≫ s.ι.app k₀ := rfl
              _ = ladderBaseLeg hT f ⊥ ≫
                  (ladderTransition hT f b ≫ s.ι.app k) := by rw [hs]
              _ = (ladderBaseLeg hT f ⊥ ≫ ladderTransition hT f b) ≫
                  s.ι.app k := (Category.assoc _ _ _).symm
              _ = ladderBaseLeg hT f k.1 ≫ s.ι.app k := by
                rw [ladderBaseLeg_transition]
        uniq := fun s t ht ↦ by
          apply sqM.hom_ext
          · rw [sqM.inl_desc]
            apply hcF.hom_ext
            intro k
            let a : k.1 ⟶ m := homOfLE k.2.le
            rw [hcF.fac]
            have htk := ht k
            change ladderTransition hT f a ≫ t = s.ι.app k at htk
            calc
              hT.F.map a ≫ (ladderComparison hT f m ≫ t) =
                  (hT.F.map a ≫ ladderComparison hT f m) ≫ t :=
                (Category.assoc _ _ _).symm
              _ = (ladderComparison hT f k.1 ≫ ladderTransition hT f a) ≫ t := by
                rw [ladderComparison_transition]
              _ = ladderComparison hT f k.1 ≫ (ladderTransition hT f a ≫ t) :=
                Category.assoc _ _ _
              _ = ladderComparison hT f k.1 ≫ s.ι.app k := by rw [htk]
          · rw [sqM.inr_desc]
            have ht₀ := ht k₀
            change ladderTransition hT f
              (homOfLE hm.bot_lt.le : (⊥ : J) ⟶ m) ≫ t = s.ι.app k₀ at ht₀
            have hbase := ladderBaseLeg_transition hT f
              (homOfLE hm.bot_lt.le : (⊥ : J) ⟶ m)
            calc
              ladderBaseLeg hT f m ≫ t =
                  (ladderBaseLeg hT f ⊥ ≫
                    ladderTransition hT f (homOfLE hm.bot_lt.le : (⊥ : J) ⟶ m)) ≫ t := by
                rw [hbase]
              _ = ladderBaseLeg hT f ⊥ ≫
                  (ladderTransition hT f (homOfLE hm.bot_lt.le : (⊥ : J) ⟶ m) ≫ t) :=
                Category.assoc _ _ _
              _ = ladderBaseLeg hT f ⊥ ≫ s.ι.app k₀ := by rw [ht₀]
              _ = baseDesc s := rfl }⟩

private theorem transfinite_incl_bot
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i) :
    hT.incl.app ⊥ = hT.isoBot.hom ≫ i := by
  calc
    hT.incl.app ⊥ = 𝟙 _ ≫ hT.incl.app ⊥ := (Category.id_comp _).symm
    _ = (hT.isoBot.hom ≫ hT.isoBot.inv) ≫ hT.incl.app ⊥ := by
      rw [hT.isoBot.hom_inv_id]
    _ = hT.isoBot.hom ≫ (hT.isoBot.inv ≫ hT.incl.app ⊥) :=
      Category.assoc _ _ _
    _ = hT.isoBot.hom ≫ i := by rw [hT.fac]

private noncomputable def ladderInclApp
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) (k : J) : ladderObj hT f k ⟶ Y :=
  (IsPushout.of_hasPushout (ladderBottomToStage hT k) (ladderBottomMap hT f)).desc
    (hT.incl.app k ≫ f') j (by
      have hn := hT.incl.naturality (homOfLE bot_le : (⊥ : J) ⟶ k)
      simp only [Functor.const_obj_map] at hn
      have hn₀ : ladderBottomToStage hT k ≫ hT.incl.app k = hT.incl.app ⊥ :=
        hn.trans (Category.comp_id _)
      calc
        ladderBottomToStage hT k ≫ (hT.incl.app k ≫ f') =
            (ladderBottomToStage hT k ≫ hT.incl.app k) ≫ f' :=
          (Category.assoc _ _ _).symm
        _ = hT.incl.app ⊥ ≫ f' := by
          exact congrArg (fun z ↦ z ≫ f') hn₀
        _ = (hT.isoBot.hom ≫ i) ≫ f' := by rw [transfinite_incl_bot]
        _ = hT.isoBot.hom ≫ (i ≫ f') := Category.assoc _ _ _
        _ = hT.isoBot.hom ≫ (f ≫ j) := by rw [outer.w]
        _ = ladderBottomMap hT f ≫ j := by
          simp [ladderBottomMap, Category.assoc])

@[reassoc]
private theorem ladderComparison_inclApp
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) (k : J) :
    ladderComparison hT f k ≫ ladderInclApp hT f f' j outer k =
      hT.incl.app k ≫ f' :=
  (IsPushout.of_hasPushout (ladderBottomToStage hT k)
    (ladderBottomMap hT f)).inl_desc _ _ _

@[reassoc]
private theorem ladderBaseLeg_inclApp
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) (k : J) :
    ladderBaseLeg hT f k ≫ ladderInclApp hT f f' j outer k = j :=
  (IsPushout.of_hasPushout (ladderBottomToStage hT k)
    (ladderBottomMap hT f)).inr_desc _ _ _

private noncomputable def ladderIncl
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) : ladderFunctor hT f ⟶ (Functor.const J).obj Y where
  app k := ladderInclApp hT f f' j outer k
  naturality k l a := by
    apply (IsPushout.of_hasPushout (ladderBottomToStage hT k)
      (ladderBottomMap hT f)).hom_ext
    · have hn := hT.incl.naturality a
      simp only [Functor.const_obj_map] at hn
      have hn₀ : hT.F.map a ≫ hT.incl.app l = hT.incl.app k :=
        hn.trans (Category.comp_id _)
      calc
        ladderComparison hT f k ≫
            (ladderTransition hT f a ≫ ladderInclApp hT f f' j outer l) =
          (ladderComparison hT f k ≫ ladderTransition hT f a) ≫
            ladderInclApp hT f f' j outer l := (Category.assoc _ _ _).symm
        _ = (hT.F.map a ≫ ladderComparison hT f l) ≫
            ladderInclApp hT f f' j outer l := by rw [ladderComparison_transition]
        _ = hT.F.map a ≫
            (ladderComparison hT f l ≫ ladderInclApp hT f f' j outer l) :=
          Category.assoc _ _ _
        _ = hT.F.map a ≫ (hT.incl.app l ≫ f') := by
          rw [ladderComparison_inclApp]
        _ = (hT.F.map a ≫ hT.incl.app l) ≫ f' :=
          (Category.assoc _ _ _).symm
        _ = hT.incl.app k ≫ f' := by rw [hn₀]
        _ = ladderComparison hT f k ≫ ladderInclApp hT f f' j outer k := by
          rw [ladderComparison_inclApp]
        _ = (ladderComparison hT f k ≫ ladderInclApp hT f f' j outer k) ≫
            ((Functor.const J).obj Y).map a := (Category.comp_id _).symm
    · calc
        ladderBaseLeg hT f k ≫
            (ladderTransition hT f a ≫ ladderInclApp hT f f' j outer l) =
          (ladderBaseLeg hT f k ≫ ladderTransition hT f a) ≫
            ladderInclApp hT f f' j outer l := (Category.assoc _ _ _).symm
        _ = ladderBaseLeg hT f l ≫ ladderInclApp hT f f' j outer l := by
          rw [ladderBaseLeg_transition]
        _ = j := ladderBaseLeg_inclApp hT f f' j outer l
        _ = ladderBaseLeg hT f k ≫ ladderInclApp hT f f' j outer k := by
          rw [ladderBaseLeg_inclApp]
        _ = (ladderBaseLeg hT f k ≫ ladderInclApp hT f f' j outer k) ≫
            ((Functor.const J).obj Y).map a := (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ladder_isColimit
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) :
    IsColimit (Cocone.mk Y (ladderIncl hT f f' j outer)) := by
  let sourceCocone (s : Cocone (ladderFunctor hT f)) : Cocone hT.F :=
    { pt := s.pt
      ι :=
        { app := fun k ↦ ladderComparison hT f k ≫ s.ι.app k
          naturality := fun k l a ↦ by
            have hc := ladderComparison_transition hT f a
            have hs := s.w a
            change hT.F.map a ≫ ladderComparison hT f l ≫ s.ι.app l =
              (ladderComparison hT f k ≫ s.ι.app k) ≫ 𝟙 s.pt
            calc
              hT.F.map a ≫ ladderComparison hT f l ≫ s.ι.app l =
                  (hT.F.map a ≫ ladderComparison hT f l) ≫ s.ι.app l :=
                (Category.assoc _ _ _).symm
              _ = (ladderComparison hT f k ≫ ladderTransition hT f a) ≫
                  s.ι.app l := by rw [hc]
              _ = ladderComparison hT f k ≫
                  (ladderTransition hT f a ≫ s.ι.app l) := Category.assoc _ _ _
              _ = ladderComparison hT f k ≫ s.ι.app k := by rw [hs]
              _ = (ladderComparison hT f k ≫ s.ι.app k) ≫ 𝟙 s.pt :=
                (Category.comp_id _).symm } }
  let sourceDesc (s : Cocone (ladderFunctor hT f)) : B ⟶ s.pt :=
    hT.isColimit.desc (sourceCocone s)
  let baseDesc (s : Cocone (ladderFunctor hT f)) : X ⟶ s.pt :=
    ladderBaseLeg hT f ⊥ ≫ s.ι.app ⊥
  have hBottomComparison : hT.isoBot.inv ≫ ladderComparison hT f ⊥ =
      f ≫ ladderBaseLeg hT f ⊥ := by
    have hu : ladderBottomToStage hT ⊥ = 𝟙 (hT.F.obj ⊥) := by
      dsimp [ladderBottomToStage]
      rw [hT.F.map_id]
    have hc : ladderComparison hT f ⊥ =
        ladderBottomMap hT f ≫ ladderBaseLeg hT f ⊥ := by
      calc
        ladderComparison hT f ⊥ = 𝟙 (hT.F.obj ⊥) ≫
            ladderComparison hT f ⊥ := (Category.id_comp _).symm
        _ = ladderBottomToStage hT ⊥ ≫ ladderComparison hT f ⊥ :=
          congrArg (fun z ↦ z ≫ ladderComparison hT f ⊥) hu.symm
        _ = ladderBottomMap hT f ≫ ladderBaseLeg hT f ⊥ := pushout.condition
    rw [hc]
    simp [ladderBottomMap, Category.assoc]
  have compat (s : Cocone (ladderFunctor hT f)) :
      i ≫ sourceDesc s = f ≫ baseDesc s := by
    have hfac := hT.isColimit.fac (sourceCocone s) ⊥
    calc
      i ≫ sourceDesc s =
          (hT.isoBot.inv ≫ hT.incl.app ⊥) ≫ sourceDesc s := by rw [hT.fac]
      _ = hT.isoBot.inv ≫ (hT.incl.app ⊥ ≫ sourceDesc s) :=
        Category.assoc _ _ _
      _ = hT.isoBot.inv ≫ (ladderComparison hT f ⊥ ≫ s.ι.app ⊥) := by
        rw [hfac]
      _ = (hT.isoBot.inv ≫ ladderComparison hT f ⊥) ≫ s.ι.app ⊥ :=
        (Category.assoc _ _ _).symm
      _ = (f ≫ ladderBaseLeg hT f ⊥) ≫ s.ι.app ⊥ := by
        rw [hBottomComparison]
      _ = f ≫ baseDesc s := Category.assoc _ _ _
  refine
    { desc := fun s ↦ outer.desc (sourceDesc s) (baseDesc s) (compat s)
      fac := fun s k ↦ by
        apply (IsPushout.of_hasPushout (ladderBottomToStage hT k)
          (ladderBottomMap hT f)).hom_ext
        · calc
            ladderComparison hT f k ≫
                (ladderInclApp hT f f' j outer k ≫
                  outer.desc (sourceDesc s) (baseDesc s) (compat s)) =
              (ladderComparison hT f k ≫ ladderInclApp hT f f' j outer k) ≫
                outer.desc (sourceDesc s) (baseDesc s) (compat s) :=
              (Category.assoc _ _ _).symm
            _ = (hT.incl.app k ≫ f') ≫
                outer.desc (sourceDesc s) (baseDesc s) (compat s) := by
              rw [ladderComparison_inclApp]
            _ = hT.incl.app k ≫
                (f' ≫ outer.desc (sourceDesc s) (baseDesc s) (compat s)) :=
              Category.assoc _ _ _
            _ = hT.incl.app k ≫ sourceDesc s := by rw [outer.inl_desc]
            _ = ladderComparison hT f k ≫ s.ι.app k :=
              hT.isColimit.fac (sourceCocone s) k
        · let a : (⊥ : J) ⟶ k := homOfLE bot_le
          have hs := s.w a
          change ladderTransition hT f a ≫ s.ι.app k = s.ι.app ⊥ at hs
          calc
            ladderBaseLeg hT f k ≫
                (ladderInclApp hT f f' j outer k ≫
                  outer.desc (sourceDesc s) (baseDesc s) (compat s)) =
              (ladderBaseLeg hT f k ≫ ladderInclApp hT f f' j outer k) ≫
                outer.desc (sourceDesc s) (baseDesc s) (compat s) :=
              (Category.assoc _ _ _).symm
            _ = j ≫ outer.desc (sourceDesc s) (baseDesc s) (compat s) := by
              rw [ladderBaseLeg_inclApp]
            _ = baseDesc s := outer.inr_desc _ _ _
            _ = ladderBaseLeg hT f ⊥ ≫ s.ι.app ⊥ := rfl
            _ = ladderBaseLeg hT f ⊥ ≫
                (ladderTransition hT f a ≫ s.ι.app k) := by rw [hs]
            _ = (ladderBaseLeg hT f ⊥ ≫ ladderTransition hT f a) ≫
                s.ι.app k := (Category.assoc _ _ _).symm
            _ = ladderBaseLeg hT f k ≫ s.ι.app k := by
              rw [ladderBaseLeg_transition]
      uniq := fun s t ht ↦ by
        apply outer.hom_ext
        · rw [outer.inl_desc]
          apply hT.isColimit.hom_ext
          intro k
          rw [hT.isColimit.fac]
          have htk := ht k
          change ladderInclApp hT f f' j outer k ≫ t = s.ι.app k at htk
          calc
            hT.incl.app k ≫ (f' ≫ t) =
                (hT.incl.app k ≫ f') ≫ t := (Category.assoc _ _ _).symm
            _ = (ladderComparison hT f k ≫ ladderInclApp hT f f' j outer k) ≫ t := by
              rw [ladderComparison_inclApp]
            _ = ladderComparison hT f k ≫
                (ladderInclApp hT f f' j outer k ≫ t) := Category.assoc _ _ _
            _ = ladderComparison hT f k ≫ s.ι.app k := by rw [htk]
        · rw [outer.inr_desc]
          have ht₀ := ht ⊥
          change ladderInclApp hT f f' j outer ⊥ ≫ t = s.ι.app ⊥ at ht₀
          calc
            j ≫ t = (ladderBaseLeg hT f ⊥ ≫
                ladderInclApp hT f f' j outer ⊥) ≫ t := by
              rw [ladderBaseLeg_inclApp]
            _ = ladderBaseLeg hT f ⊥ ≫
                (ladderInclApp hT f f' j outer ⊥ ≫ t) := Category.assoc _ _ _
            _ = ladderBaseLeg hT f ⊥ ≫ s.ι.app ⊥ := by rw [ht₀]
            _ = baseDesc s := rfl }

private theorem ladder_comparison_fac
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) :
    hT.incl ≫ (Functor.const J).map f' =
      ladderComparisonNat hT f ≫ ladderIncl hT f f' j outer := by
  apply NatTrans.ext
  funext k
  exact (ladderComparison_inclApp hT f f' j outer k).symm

private noncomputable def relativeCellCobaseLadder
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B} {R : MorphismProperty TopCat.{u}}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) : RelativeCellCobaseLadder hT f f' j where
  outerPushout := outer
  G := ladderFunctor hT f
  comparison := ladderComparisonNat hT f
  isoBot := ladderIsoBot hT f
  bottomComparison := ladder_bottomComparison hT f
  isWellOrderContinuous := ladder_isWellOrderContinuous hT f
  successorPushout := ladder_successorPushout hT f
  incl := ladderIncl hT f f' j outer
  isColimit := ladder_isColimit hT f f' j outer
  comparison_fac := ladder_comparison_fac hT f f' j outer

private theorem relativeCellCobaseLadder_exists
    (R : MorphismProperty TopCat.{u}) :
    ∀ {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
      {A B X Y : TopCat.{u}} {i : A ⟶ B}
      (hT : R.TransfiniteCompositionOfShape J i)
      (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y),
      IsPushout i f f' j → Nonempty (RelativeCellCobaseLadder hT f f' j) := by
  intro J _ _ _ _ A B X Y i hT f f' j outer
  exact ⟨relativeCellCobaseLadder hT f f' j outer⟩

private theorem closedT1LadderLimit
    {J : Type u} [LinearOrder J] [OrderBot J]
    {F G : J ⥤ TopCat.{u}} (a : F ⟶ G)
    (cF : Cocone F) (cG : Cocone G)
    (hF : IsColimit cF) (hG : IsColimit cG)
    (hContF : F.IsWellOrderContinuous) (hContG : G.IsWellOrderContinuous)
    (hClosedF : ∀ {k l : J} (g : k ⟶ l), TopCat.closedT1Embeddings (F.map g))
    (hClosedG : ∀ {k l : J} (g : k ⟶ l), TopCat.closedT1Embeddings (G.map g))
    (ha : ∀ k, W (a.app k)) :
    W (hF.desc (Cocone.mk cG.pt (a ≫ cG.ι))) := by
  let _ : F.IsWellOrderContinuous := hContF
  let _ : G.IsWellOrderContinuous := hContG
  let hMappedContF : (F ⋙ TopCat.toSSet.{u}).IsWellOrderContinuous :=
    TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite
      (fun {_ _} g ↦ hClosedF g)
  let hMappedContG : (G ⋙ TopCat.toSSet.{u}).IsWellOrderContinuous :=
    TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite
      (fun {_ _} g ↦ hClosedG g)
  let _ : (F ⋙ TopCat.toSSet.{u}).IsWellOrderContinuous := hMappedContF
  let _ : (G ⋙ TopCat.toSSet.{u}).IsWellOrderContinuous := hMappedContG
  let _ : PreservesColimit F TopCat.toSSet.{u} :=
    TopCat.preservesColimit_toSSet_of_closedT1_transfinite
      (fun {_ _} g ↦ hClosedF g)
  let _ : PreservesColimit G TopCat.toSSet.{u} :=
    TopCat.preservesColimit_toSSet_of_closedT1_transfinite
      (fun {_ _} g ↦ hClosedG g)
  let cFS := TopCat.toSSet.{u}.mapCocone cF
  let cGS := TopCat.toSSet.{u}.mapCocone cG
  let hcFS : IsColimit cFS := isColimitOfPreserves TopCat.toSSet.{u} hF
  let hcGS : IsColimit cGS := isColimitOfPreserves TopCat.toSSet.{u} hG
  let b := hF.desc (Cocone.mk cG.pt (a ≫ cG.ι))
  have hbNat (k : J) : cFS.ι.app k ≫ TopCat.toSSet.map b =
      TopCat.toSSet.map (a.app k) ≫ cGS.ι.app k := by
    change TopCat.toSSet.map (cF.ι.app k) ≫ TopCat.toSSet.map b =
      TopCat.toSSet.map (a.app k) ≫ TopCat.toSSet.map (cG.ι.app k)
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
    exact congrArg TopCat.toSSet.map
      (hF.fac (Cocone.mk cG.pt (a ≫ cG.ι)) k)
  have hKan : SSet.KanComplex.W (TopCat.toSSet.map b) := by
    apply MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := SSet.KanComplex.W) (F ⋙ TopCat.toSSet.{u})
      (G ⋙ TopCat.toSSet.{u}) cFS cGS hcFS hcGS
      (Functor.whiskerRight a TopCat.toSSet.{u})
    · intro k
      exact (TopCat.mem_weakHomotopyEquivalences_iff (a.app k)).mp (ha k)
    · exact hbNat
  exact (TopCat.mem_weakHomotopyEquivalences_iff b).mpr hKan

private theorem relativeCellCobase_weak
    (R : MorphismProperty TopCat.{u})
    (hRP : R ≤ (P.{u} : MorphismProperty TopCat.{u}))
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    {A B X Y : TopCat.{u}} {i : A ⟶ B}
    (hT : R.TransfiniteCompositionOfShape J i)
    (f : A ⟶ X) (f' : B ⟶ Y) (j : X ⟶ Y)
    (outer : IsPushout i f f' j) (hf : W f) : W f' := by
  let L := relativeCellCobaseLadder hT f f' j outer
  let hFclosedTC : TopCat.closedT1Embeddings.TransfiniteCompositionOfShape J i :=
    hT.ofLE (fun _ _ g hg ↦ (hRP _ hg).2)
  have hFclosed : ∀ {k l : J} (g : k ⟶ l),
      TopCat.closedT1Embeddings (hT.F.map g) := fun {_ _} g ↦ hFclosedTC.mem_map g
  let gTot := L.isoBot.inv ≫ L.incl.app ⊥
  let hGclosedTC : TopCat.closedT1Embeddings.TransfiniteCompositionOfShape J gTot :=
    { F := L.G
      isoBot := L.isoBot
      isWellOrderContinuous := L.isWellOrderContinuous
      incl := L.incl
      isColimit := L.isColimit
      fac := rfl
      map_mem := fun k hk ↦ by
        have hs := hRP _ (hT.map_mem k hk)
        exact TopCat.closedT1Embeddings.of_isPushout
          (L.successorPushout k hk).flip hs.2 }
  have hGclosed : ∀ {k l : J} (g : k ⟶ l),
      TopCat.closedT1Embeddings (L.G.map g) := fun {_ _} g ↦ hGclosedTC.mem_map g
  have hComp : ∀ k : J, W (L.comparison.app k) := by
    intro k
    induction k using SuccOrder.limitRecOn with
    | isMin k hk =>
        obtain rfl := hk.eq_bot
        have hsq : L.comparison.app ⊥ ≫ L.isoBot.hom =
            hT.isoBot.hom ≫ f := by
          have h := L.bottomComparison
          rw [← cancel_epi hT.isoBot.inv]
          simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
        let e : Arrow.mk (L.comparison.app ⊥) ≅ Arrow.mk f :=
          Arrow.isoMk hT.isoBot L.isoBot hsq.symm
        exact (W.arrow_mk_iso_iff e).2 hf
    | succ k hk ih =>
        have hs := hRP _ (hT.map_mem k hk)
        exact hs.1.of_isPushout (L.successorPushout k hk) ih
    | isSuccLimit k hk ih =>
        let K := Set.Iio k
        let _ : OrderBot K :=
          { bot := ⟨⊥, hk.bot_lt⟩
            bot_le := fun _ ↦ bot_le }
        let inc := (Set.principalSegIio k).monotone.functor
        let Fk := inc ⋙ hT.F
        let Gk := inc ⋙ L.G
        let ak : Fk ⟶ Gk := Functor.whiskerLeft inc L.comparison
        let cFk := (Set.principalSegIio k).cocone hT.F
        let cGk := (Set.principalSegIio k).cocone L.G
        let hcFk : IsColimit cFk := hT.F.isColimitOfIsWellOrderContinuous k hk
        let hcGk : IsColimit cGk :=
          let _ : L.G.IsWellOrderContinuous := L.isWellOrderContinuous
          L.G.isColimitOfIsWellOrderContinuous k hk
        let b := hcFk.desc (Cocone.mk cGk.pt (ak ≫ cGk.ι))
        have hb : b = L.comparison.app k := by
          apply hcFk.hom_ext
          intro l
          rw [hcFk.fac]
          exact (NatTrans.naturality L.comparison (homOfLE l.2.le)).symm
        have hbW : W b := by
          apply closedT1LadderLimit ak cFk cGk hcFk hcGk
          · let _ : hT.F.IsWellOrderContinuous :=
                hT.toTransfiniteCompositionOfShape.isWellOrderContinuous
            let e := principalSegToInitialSeg (Set.principalSegIio k)
            change (e.monotone.functor ⋙ hT.F).IsWellOrderContinuous
            infer_instance
          · let _ : L.G.IsWellOrderContinuous := L.isWellOrderContinuous
            let e := principalSegToInitialSeg (Set.principalSegIio k)
            change (e.monotone.functor ⋙ L.G).IsWellOrderContinuous
            infer_instance
          · intro l l' g
            exact hFclosed _
          · intro l l' g
            exact hGclosed _
          · intro l
            exact ih l.1 l.2
        rw [← hb]
        exact hbW
  have hFinal := closedT1LadderLimit L.comparison
    (Cocone.mk B hT.incl) (Cocone.mk Y L.incl)
    hT.isColimit L.isColimit
    hT.toTransfiniteCompositionOfShape.isWellOrderContinuous
    L.isWellOrderContinuous hFclosed hGclosed hComp
  rw [L.colimitComparison_eq] at hFinal
  exact hFinal

private theorem closedT1RelativeCellCobase
    (R : MorphismProperty TopCat.{u})
    (hRP : R ≤ (P.{u} : MorphismProperty TopCat.{u})) :
    transfiniteCompositions.{u} R ≤ (Q.{u} : MorphismProperty TopCat.{u}) := by
  intro A B i hi
  rw [transfiniteCompositions_iff] at hi
  obtain ⟨J, _, _, _, _, ⟨hT⟩⟩ := hi
  refine { of_isPushout := ?_ }
  intro X Y j k hbase outer hh
  exact relativeCellCobase_weak R hRP hT hbase k j outer hh

private theorem boundaryStages_le_closedT1 :
    (S.{u} : MorphismProperty TopCat.{u}) ≤ TopCat.closedT1Embeddings.{u} := by
  calc
    (S.{u} : MorphismProperty TopCat.{u}) ≤
        (coproducts.{u}
          (TopCat.realizedBoundaryInclusions.{u} ⊔
            TopCat.realizedHornInclusions.{u})).pushouts :=
      MorphismProperty.pushouts_monotone
        (MorphismProperty.coproducts_monotone le_sup_left)
    _ ≤ TopCat.closedT1Embeddings.{u} :=
      TopCat.pushouts_coproducts_realizedGenerators_le_closedT1Embeddings

private theorem boundaryRelativeCell_DAG
    (hIpushQ : (I.{u} : MorphismProperty TopCat.{u}).pushouts ≤
      (Q.{u} : MorphismProperty TopCat.{u})) :
    transfiniteCompositions.{u} (S.{u} : MorphismProperty TopCat.{u}) ≤
      (Q.{u} : MorphismProperty TopCat.{u}) := by
  have hIpushClosed : (I.{u} : MorphismProperty TopCat.{u}).pushouts ≤
      TopCat.closedT1Embeddings.{u} :=
    MorphismProperty.pushouts_le_iff.mpr
      TopCat.realizedBoundaryInclusions_le_closedT1Embeddings
  have hIpushP : (I.{u} : MorphismProperty TopCat.{u}).pushouts ≤
      (P.{u} : MorphismProperty TopCat.{u}) :=
    fun _ _ _ hi ↦ ⟨hIpushQ _ hi, hIpushClosed _ hi⟩
  have hInner : transfiniteCompositions.{u}
      (I.{u} : MorphismProperty TopCat.{u}).pushouts ≤
        (Q.{u} : MorphismProperty TopCat.{u}) :=
    closedT1RelativeCellCobase _ hIpushP
  have hStageQ : (S.{u} : MorphismProperty TopCat.{u}) ≤
      (Q.{u} : MorphismProperty TopCat.{u}) :=
    boundaryPushedCoproducts_le_transfiniteBoundaryPushouts.trans hInner
  have hStageP : (S.{u} : MorphismProperty TopCat.{u}) ≤
      (P.{u} : MorphismProperty TopCat.{u}) :=
    fun _ _ _ hs ↦ ⟨hStageQ _ hs, boundaryStages_le_closedT1 _ hs⟩
  exact closedT1RelativeCellCobase _ hStageP

private local instance boundarySmallObjectκ_isRegular :
    Fact (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ.IsRegular :=
  HasSmallObjectArgument.exists_cardinal.choose_spec.choose

private noncomputable def boundarySmallObjectFactorization {X Y : TopCat.{u}}
    (i : X ⟶ Y) :
    MapFactorizationData
      (transfiniteCompositions.{u} (S.{u} : MorphismProperty TopCat.{u}))
      (I.{u} : MorphismProperty TopCat.{u}).rlp i where
  Z := SmallObject.obj (I.{u} : MorphismProperty TopCat.{u})
    (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ i
  i := SmallObject.ιObj (I.{u} : MorphismProperty TopCat.{u})
    (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ i
  p := SmallObject.πObj (I.{u} : MorphismProperty TopCat.{u})
    (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ i
  fac := SmallObject.ιObj_πObj (I.{u} : MorphismProperty TopCat.{u})
    (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ i
  hi := by
    apply transfiniteCompositionsOfShape_le_transfiniteCompositions
      (S.{u} : MorphismProperty TopCat.{u})
      (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ.ord.ToType
    simpa only [S] using
      SmallObject.transfiniteCompositionsOfShape_ιObj
        (I.{u} : MorphismProperty TopCat.{u})
        (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ i
  hp := SmallObject.rlp_πObj (I.{u} : MorphismProperty TopCat.{u})
    (I.{u} : MorphismProperty TopCat.{u}).smallObjectκ i

private structure SameSourceArrowRetract {C : Type u₁} [Category.{v₁} C]
    {X Y Z : C} (i : X ⟶ Y) (c : X ⟶ Z) where
  inclusion : Y ⟶ Z
  retraction : Z ⟶ Y
  inclusion_fac : i ≫ inclusion = c
  retraction_fac : c ≫ retraction = i
  retract_target : inclusion ≫ retraction = 𝟙 Y

private def SameSourceArrowRetract.toRetractArrow
    {C : Type u₁} [Category.{v₁} C] {X Y Z : C} {i : X ⟶ Y} {c : X ⟶ Z}
    (d : SameSourceArrowRetract i c) : RetractArrow i c where
  i := Arrow.homMk (𝟙 X) d.inclusion (by simp [d.inclusion_fac])
  r := Arrow.homMk (𝟙 X) d.retraction (by simp [d.retraction_fac])
  retract := by
    ext
    · simp
    · exact d.retract_target

private noncomputable def boundarySmallObjectRetract {X Y : TopCat.{u}}
    (i : X ⟶ Y) (hi : (I.{u} : MorphismProperty TopCat.{u}).rlp.llp i) :
    SameSourceArrowRetract i (boundarySmallObjectFactorization i).i := by
  let d := boundarySmallObjectFactorization i
  change SameSourceArrowRetract i d.i
  let _ : HasLiftingProperty i d.p := hi _ d.hp
  let sq : CommSq d.i i d.p (𝟙 Y) := ⟨by
    rw [Category.comp_id]
    exact d.fac⟩
  exact
    { inclusion := sq.lift
      retraction := d.p
      inclusion_fac := sq.fac_left
      retraction_fac := d.fac
      retract_target := sq.fac_right }

private noncomputable def SameSourceArrowRetract.pushoutSection
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) : Y' ⟶ Z' :=
  sqi.desc (d.inclusion ≫ kc) jc (by
    rw [← Category.assoc, d.inclusion_fac]
    exact sqc.w)

@[reassoc (attr := simp)]
private lemma SameSourceArrowRetract.ki_pushoutSection
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) :
    ki ≫ d.pushoutSection sqi sqc = d.inclusion ≫ kc := by
  simp [SameSourceArrowRetract.pushoutSection]

@[reassoc (attr := simp)]
private lemma SameSourceArrowRetract.ji_pushoutSection
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) :
    ji ≫ d.pushoutSection sqi sqc = jc := by
  simp [SameSourceArrowRetract.pushoutSection]

private noncomputable def SameSourceArrowRetract.pushoutRetraction
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) : Z' ⟶ Y' :=
  sqc.desc (d.retraction ≫ ki) ji (by
    rw [← Category.assoc, d.retraction_fac]
    exact sqi.w)

@[reassoc (attr := simp)]
private lemma SameSourceArrowRetract.kc_pushoutRetraction
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) :
    kc ≫ d.pushoutRetraction sqi sqc = d.retraction ≫ ki := by
  simp [SameSourceArrowRetract.pushoutRetraction]

@[reassoc (attr := simp)]
private lemma SameSourceArrowRetract.jc_pushoutRetraction
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) :
    jc ≫ d.pushoutRetraction sqi sqc = ji := by
  simp [SameSourceArrowRetract.pushoutRetraction]

private lemma SameSourceArrowRetract.pushoutSection_retraction
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) :
    d.pushoutSection sqi sqc ≫ d.pushoutRetraction sqi sqc = 𝟙 Y' := by
  apply sqi.hom_ext
  · rw [← Category.assoc, d.ki_pushoutSection, Category.assoc,
      d.kc_pushoutRetraction, ← Category.assoc, d.retract_target,
      Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, d.ji_pushoutSection, d.jc_pushoutRetraction,
      Category.comp_id]

private noncomputable def SameSourceArrowRetract.pushoutLegRetract
    {C : Type u₁} [Category.{v₁} C] {X Y Z X' Y' Z' : C}
    {i : X ⟶ Y} {c : X ⟶ Z} (d : SameSourceArrowRetract i c)
    {h : X ⟶ X'} {ki : Y ⟶ Y'} {ji : X' ⟶ Y'}
    {kc : Z ⟶ Z'} {jc : X' ⟶ Z'}
    (sqi : IsPushout i h ki ji) (sqc : IsPushout c h kc jc) :
    RetractArrow ki kc where
  i := Arrow.homMk d.inclusion (d.pushoutSection sqi sqc) (by simp)
  r := Arrow.homMk d.retraction (d.pushoutRetraction sqi sqc) (by simp)
  retract := by
    ext
    · exact d.retract_target
    · exact d.pushoutSection_retraction sqi sqc

private theorem boundaryGeneratedLeftClass_le_Q
    (hRelative : transfiniteCompositions.{u}
      (S.{u} : MorphismProperty TopCat.{u}) ≤ (Q.{u} : MorphismProperty TopCat.{u})) :
    (I.{u} : MorphismProperty TopCat.{u}).rlp.llp ≤
      (Q.{u} : MorphismProperty TopCat.{u}) := by
  intro X Y i hi
  refine { of_isPushout := ?_ }
  intro X' Y' j k h sq hh
  let d := boundarySmallObjectFactorization i
  have hcQ : (Q.{u} : MorphismProperty TopCat.{u}) d.i := hRelative _ d.hi
  have sqc : IsPushout d.i h (pushout.inl d.i h) (pushout.inr d.i h) :=
    IsPushout.of_hasPushout d.i h
  have hkc : (W.{u} : MorphismProperty TopCat.{u}) (pushout.inl d.i h) :=
    hcQ.of_isPushout sqc hh
  let r : SameSourceArrowRetract i d.i := by
    simpa only [d] using boundarySmallObjectRetract i hi
  exact MorphismProperty.of_retract (r.pushoutLegRetract sq sqc) hkc

private theorem selectedIsLeftProperOfRelativeCell
    (hRelative : transfiniteCompositions.{u}
      (S.{u} : MorphismProperty TopCat.{u}) ≤ (Q.{u} : MorphismProperty TopCat.{u})) :
    IsLeftProper TopCat.{u} where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    change (W.{u} : MorphismProperty TopCat.{u}).IsStableUnderCobaseChangeAgainst
      (I.{u} : MorphismProperty TopCat.{u}).rlp.llp
    constructor
    intro A B i hi
    exact boundaryGeneratedLeftClass_le_Q hRelative i hi

private theorem selectedIsLeftProperOfBoundaryPushouts
    (hIpushQ : (I.{u} : MorphismProperty TopCat.{u}).pushouts ≤
      (Q.{u} : MorphismProperty TopCat.{u})) : IsLeftProper TopCat.{u} :=
  selectedIsLeftProperOfRelativeCell (boundaryRelativeCell_DAG hIpushQ)

private def oneCellOldOpen {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) : Set s.Y :=
  (s.f' ''
    (RealizedSimplexBoundaryCutoff.thickening n
      (boundaryThickeningLevel n))ᶜ)ᶜ

private def oneCellCellOpen {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) : Set s.Y :=
  (Set.range s.j.hom)ᶜ

private theorem oneCellCellOpen_isOpen {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    IsOpen (oneCellCellOpen s) := by
  exact TopCat.isOpen_oneCellOpenComplement
    (isClosedEmbedding_simplexCell_oldLeg s.isPushout.flip)

private theorem oneCell_oldRange_subset_oldOpen {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    Set.range s.j.hom ⊆ oneCellOldOpen s := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  unfold oneCellOldOpen
  rw [Set.mem_compl_iff]
  rintro ⟨q, hqCompl, hqeq⟩
  have hqNotPre :
      q ∉ s.f' ⁻¹' oneCellCellOpen s := by
    intro hq
    apply (Set.mem_compl_iff _ _).mp hq
    exact ⟨x, hqeq.symm⟩
  have hpre :=
    TopCat.preimage_oneCellOpenComplement_eq s.isPushout.flip
  change s.f' ⁻¹' (Set.range s.j.hom)ᶜ =
      (Set.range (boundaryCell n).hom)ᶜ at hpre
  change q ∉ s.f' ⁻¹' (Set.range s.j.hom)ᶜ at hqNotPre
  rw [hpre] at hqNotPre
  have hqRange : q ∈ Set.range (boundaryCell n).hom := by
    by_contra hqNot
    exact hqNotPre ((Set.mem_compl_iff _ _).mpr hqNot)
  have hqThick : q ∈
      RealizedSimplexBoundaryCutoff.thickening n
        (boundaryThickeningLevel n) :=
    (RealizedSimplexBoundaryCutoff.range_subset_thickening n
      (boundaryThickeningLevel_pos n)) hqRange
  exact ((Set.mem_compl_iff _ _).mp hqCompl) hqThick

private theorem oneCellOpenCover {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    Set.univ ⊆ oneCellOldOpen s ∪ oneCellCellOpen s := by
  intro y _hy
  by_cases hy : y ∈ Set.range s.j.hom
  · exact Set.mem_union_left _ (oneCell_oldRange_subset_oldOpen s hy)
  · exact Set.mem_union_right _ ((Set.mem_compl_iff _ _).mpr hy)

private theorem oneCellOldOpen_cell_preimage {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    s.f' ⁻¹' oneCellOldOpen s =
      RealizedSimplexBoundaryCutoff.thickening n
        (boundaryThickeningLevel n) := by
  apply Set.Subset.antisymm
  · intro q hq
    by_contra hqNot
    unfold oneCellOldOpen at hq
    apply (Set.mem_compl_iff _ _).mp hq
    refine ⟨q, (Set.mem_compl_iff _ _).mpr hqNot, rfl⟩
  · intro q hq
    change s.f' q ∈
      (s.f' ''
        (RealizedSimplexBoundaryCutoff.thickening n
          (boundaryThickeningLevel n))ᶜ)ᶜ
    rw [Set.mem_compl_iff]
    rintro ⟨q', hq'Compl, hq'eq⟩
    have hq'NotRange : q' ∉ Set.range (boundaryCell n).hom := by
      intro hq'Range
      have hq'Thick : q' ∈
          RealizedSimplexBoundaryCutoff.thickening n
            (boundaryThickeningLevel n) :=
        (RealizedSimplexBoundaryCutoff.range_subset_thickening n
          (boundaryThickeningLevel_pos n)) hq'Range
      exact ((Set.mem_compl_iff _ _).mp hq'Compl) hq'Thick
    have hq'eq_q : q' = q := by
      apply
        CategoryTheory.Limits.Types.pushoutCocone_inr_eq_inr_of_not_mem_range_of_isColimit
          (s.isPushout.flip.map (forget TopCat)).isColimit hq'NotRange
      exact hq'eq
    subst q'
    exact ((Set.mem_compl_iff _ _).mp hq'Compl) hq

private theorem oneCellOldOpen_old_preimage {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    s.j ⁻¹' oneCellOldOpen s = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact oneCell_oldRange_subset_oldOpen s ⟨x, rfl⟩

private theorem oneCellOldOpen_isOpen {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    IsOpen (oneCellOldOpen s) := by
  have hCell : IsOpen (s.f' ⁻¹' oneCellOldOpen s) := by
    rw [oneCellOldOpen_cell_preimage]
    exact RealizedSimplexBoundaryCutoff.isOpen_thickening n
      (boundaryThickeningLevel n)
  have hOld : IsOpen (s.j ⁻¹' oneCellOldOpen s) := by
    rw [oneCellOldOpen_old_preimage]
    exact isOpen_univ
  refine (TopCat.isOpen_iff_of_isColimit
    s.isPushout.cocone s.isPushout.isColimit
      (oneCellOldOpen s)).2 ?_
  rintro (_ | _ | _)
  · exact hCell.preimage (boundaryCell n).hom.continuous
  · exact hCell
  · exact hOld

private theorem boundaryNeighborhoodHomotopy_mem
    (n : ℕ) (t : unitInterval)
    (q : boundaryNeighborhood.{u} n) :
    boundaryNeighborhoodHomotopy n (t, q) ∈
      RealizedSimplexBoundaryCutoff.thickening n
        (boundaryThickeningLevel n) := by
  change (SimplexCategory.mk n).toTopHomeo.symm
      (StdSimplexRadialBoundary.homotopyPoint n t
        ((SimplexCategory.mk n).toTopHomeo q.val)
        (boundaryNeighborhood_std_ne_barycenter n q)) ∈
    RealizedSimplexBoundaryCutoff.thickening n
      (boundaryThickeningLevel n)
  exact RealizedSimplexBoundaryCutoff.homotopyPoint_mem_thickening_of_mem
    n (boundaryThickeningLevel n) t q.val
      (boundaryNeighborhood_std_ne_barycenter n q) q.property

private def oneCellOldRestriction {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) : TopCat.RestrictedPushout.{u} :=
  TopCat.RestrictedPushout.of s.isPushout (oneCellOldOpen s)

private noncomputable def oneCellOldCellToBoundaryNeighborhood {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    C((oneCellOldRestriction s).obj₂, boundaryNeighborhood.{u} n) where
  toFun q := ⟨q.val, by
    have hq : q.val ∈ s.f' ⁻¹' oneCellOldOpen s := q.property
    rw [oneCellOldOpen_cell_preimage] at hq
    exact hq⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

private noncomputable def oneCellOldRetraction {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    (oneCellOldRestriction s).obj₂ ⟶
      (oneCellOldRestriction s).obj₁ :=
  TopCat.ofHom
    { toFun := fun q =>
        ⟨boundaryNeighborhoodRetraction n
            (oneCellOldCellToBoundaryNeighborhood s q), by
          change (boundaryCell n ≫ s.f')
            (boundaryNeighborhoodRetraction n
              (oneCellOldCellToBoundaryNeighborhood s q)) ∈
                oneCellOldOpen s
          rw [s.isPushout.w]
          exact oneCell_oldRange_subset_oldOpen s
            ⟨s.f (boundaryNeighborhoodRetraction n
              (oneCellOldCellToBoundaryNeighborhood s q)), rfl⟩⟩
      continuous_toFun := Continuous.subtype_mk
        ((boundaryNeighborhoodRetraction n).hom.continuous.comp
          (oneCellOldCellToBoundaryNeighborhood s).continuous) _ }

private theorem oneCellOldRetraction_retract {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    (oneCellOldRestriction s).tU ≫ oneCellOldRetraction s =
      𝟙 (oneCellOldRestriction s).obj₁ := by
  apply TopCat.hom_ext
  ext x
  let qN := oneCellOldCellToBoundaryNeighborhood s
    ((oneCellOldRestriction s).tU x)
  change SSet.realizedBoundaryRadialRetraction n
      (boundaryNeighborhoodToComplement n qN) = x.val
  have h := SSet.realizedBoundaryRadialRetraction_on_boundary n x.val
    (boundaryNeighborhood_ne_barycenter n qN)
  let z : {q : SSet.toTop.obj (Δ[n] : SSet.{u}) //
      q ≠ SSet.realizedBarycenter n} :=
    ⟨SSet.toTop.map (SSet.boundary.{u} n).ι x.val,
      boundaryNeighborhood_ne_barycenter n qN⟩
  have hz : boundaryNeighborhoodToComplement n qN = z := by
    apply Subtype.ext
    rfl
  rw [hz]
  exact h

private noncomputable def oneCellOldHomotopy {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    TopCat.Homotopy (𝟙 (oneCellOldRestriction s).obj₂)
      (oneCellOldRetraction s ≫ (oneCellOldRestriction s).tU) where
  toFun p :=
    ⟨boundaryNeighborhoodHomotopy n
      (p.1, oneCellOldCellToBoundaryNeighborhood s p.2), by
        have hmem := boundaryNeighborhoodHomotopy_mem n p.1
          (oneCellOldCellToBoundaryNeighborhood s p.2)
        have hpre := oneCellOldOpen_cell_preimage s
        exact hpre.symm.subset hmem⟩
  continuous_toFun := Continuous.subtype_mk
    ((boundaryNeighborhoodHomotopy n).continuous.comp
      (continuous_fst.prodMk
        ((oneCellOldCellToBoundaryNeighborhood s).continuous.comp
          continuous_snd))) _
  map_zero_left := by
    intro q
    apply Subtype.ext
    exact (boundaryNeighborhoodHomotopy n).map_zero_left
      (oneCellOldCellToBoundaryNeighborhood s q)
  map_one_left := by
    intro q
    apply Subtype.ext
    exact (boundaryNeighborhoodHomotopy n).map_one_left
      (oneCellOldCellToBoundaryNeighborhood s q)

private theorem oneCellOldHomotopy_fixed {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) (t : unitInterval)
    (x : (oneCellOldRestriction s).obj₁) :
    oneCellOldHomotopy s (t, (oneCellOldRestriction s).tU x) =
      (oneCellOldRestriction s).tU x := by
  apply Subtype.ext
  exact boundaryNeighborhoodHomotopy_fixed n t x.val
    (oneCellOldCellToBoundaryNeighborhood s
      ((oneCellOldRestriction s).tU x)).property

private theorem oneCellOldInclusion_mem_W {n : ℕ}
    (s : BoundaryOneCellSquare.{u} n) :
    W (oneCellOldRestriction s).bU := by
  exact TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences
    ((oneCellOldRestriction s).isPushout (oneCellOldOpen_isOpen s))
    (oneCellOldRetraction s) (oneCellOldRetraction_retract s)
    (oneCellOldHomotopy s) (oneCellOldHomotopy_fixed s)

private def BoundaryOneCellAttachmentCube.outerSquare {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    BoundaryOneCellSquare.{u} n where
  X := c.X'
  Y := c.Y'
  f := c.upper.f ≫ c.h
  f' := c.upper.f' ≫ c.k
  j := c.j'
  isPushout := c.outerPushout

set_option backward.isDefEq.respectTransparency false in
private theorem cube_sourceOld_eq {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    c.k ⁻¹' oneCellOldOpen c.outerSquare =
      oneCellOldOpen c.upper := by
  ext y
  obtain ⟨q, rfl⟩ | ⟨x, rfl⟩ :=
    CategoryTheory.Limits.Types.eq_or_eq_of_isPushout
      (c.upper.isPushout.map (forget TopCat)) y
  · change q ∈ (c.upper.f' ≫ c.k) ⁻¹'
        oneCellOldOpen c.outerSquare ↔
      q ∈ c.upper.f' ⁻¹' oneCellOldOpen c.upper
    have hOuter : (c.upper.f' ≫ c.k) ⁻¹'
        (oneCellOldOpen c.outerSquare : Set c.Y') =
          RealizedSimplexBoundaryCutoff.thickening n
            (boundaryThickeningLevel n) := by
      simpa only [BoundaryOneCellAttachmentCube.outerSquare] using
        oneCellOldOpen_cell_preimage c.outerSquare
    rw [hOuter, oneCellOldOpen_cell_preimage]
  · have hLeft : c.k (c.upper.j x) ∈
        oneCellOldOpen c.outerSquare := by
      change (c.upper.j ≫ c.k) x ∈
        oneCellOldOpen c.outerSquare
      rw [c.lowerPushout.w]
      exact oneCell_oldRange_subset_oldOpen c.outerSquare
        ⟨c.h x, rfl⟩
    have hRight : c.upper.j x ∈ oneCellOldOpen c.upper :=
      oneCell_oldRange_subset_oldOpen c.upper ⟨x, rfl⟩
    exact iff_of_true hLeft hRight

private theorem cube_lowerOldSource_eq {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    (c.upper.j ≫ c.k) ⁻¹' oneCellOldOpen c.outerSquare =
      c.upper.j ⁻¹' oneCellOldOpen c.upper := by
  ext x
  change c.upper.j x ∈ c.k ⁻¹' oneCellOldOpen c.outerSquare ↔
    c.upper.j x ∈ oneCellOldOpen c.upper
  rw [cube_sourceOld_eq]

private def cubeLowerOldRestriction {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    TopCat.RestrictedPushout.{u} :=
  TopCat.RestrictedPushout.of c.lowerPushout
    (oneCellOldOpen c.outerSquare)

private theorem cubeLowerOld_bU_eq {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    (cubeLowerOldRestriction c).bU =
      (oneCellOldRestriction c.outerSquare).bU := by
  rfl

private theorem cubeLowerOld_top_mem_W {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    W (cubeLowerOldRestriction c).tU := by
  let e₁ : (cubeLowerOldRestriction c).obj₁ ≅
      (oneCellOldRestriction c.upper).obj₃ :=
    TopCat.isoOfHomeo (Homeomorph.setCongr (cube_lowerOldSource_eq c))
  let e₂ : (cubeLowerOldRestriction c).obj₂ ≅
      (oneCellOldRestriction c.upper).obj₄ :=
    TopCat.isoOfHomeo (Homeomorph.setCongr (cube_sourceOld_eq c))
  have hcomm : e₁.hom ≫ (oneCellOldRestriction c.upper).bU =
      (cubeLowerOldRestriction c).tU ≫ e₂.hom := by
    apply TopCat.hom_ext
    ext x
    rfl
  let e : Arrow.mk (cubeLowerOldRestriction c).tU ≅
      Arrow.mk (oneCellOldRestriction c.upper).bU :=
    Arrow.isoMk e₁ e₂ hcomm
  exact (W.arrow_mk_iso_iff e).2 (oneCellOldInclusion_mem_W c.upper)

private theorem cubeLowerOld_obj₁_univ {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    (c.upper.j ≫ c.k) ⁻¹' oneCellOldOpen c.outerSquare =
      Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  change (c.upper.j ≫ c.k) x ∈ oneCellOldOpen c.outerSquare
  rw [c.lowerPushout.w]
  exact oneCell_oldRange_subset_oldOpen c.outerSquare ⟨c.h x, rfl⟩

private theorem cubeLowerOld_left_mem_W {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) (hh : W c.h) :
    W (cubeLowerOldRestriction c).lU := by
  let e₁ : (cubeLowerOldRestriction c).obj₁ ≅ c.upper.X :=
    TopCat.isoOfHomeo
      ((Homeomorph.setCongr (cubeLowerOld_obj₁_univ c)).trans
        (Homeomorph.Set.univ c.upper.X))
  let e₂ : (cubeLowerOldRestriction c).obj₃ ≅ c.X' :=
    TopCat.isoOfHomeo
      ((Homeomorph.setCongr
        (oneCellOldOpen_old_preimage c.outerSquare)).trans
          (Homeomorph.Set.univ c.X'))
  have hcomm : e₁.hom ≫ c.h =
      (cubeLowerOldRestriction c).lU ≫ e₂.hom := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hcomp : W ((cubeLowerOldRestriction c).lU ≫ e₂.hom) := by
    rw [← hcomm]
    exact W.comp_mem _ _ (W.of_isIso e₁.hom) hh
  exact (W.cancel_right_of_respectsIso
    (cubeLowerOldRestriction c).lU e₂.hom).mp hcomp

private theorem cubeLowerOld_right_mem_W {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) (hh : W c.h) :
    W (cubeLowerOldRestriction c).rU := by
  have htop : W (cubeLowerOldRestriction c).tU :=
    cubeLowerOld_top_mem_W c
  have hleft : W (cubeLowerOldRestriction c).lU :=
    cubeLowerOld_left_mem_W c hh
  have hbottom : W (cubeLowerOldRestriction c).bU := by
    rw [cubeLowerOld_bU_eq]
    exact oneCellOldInclusion_mem_W c.outerSquare
  have hcomp : W ((cubeLowerOldRestriction c).tU ≫
      (cubeLowerOldRestriction c).rU) := by
    rw [(cubeLowerOldRestriction c).w]
    exact W.comp_mem _ _ hleft hbottom
  exact W.of_precomp _ _ htop hcomp

private theorem subspaceMap_preimage_mem_W_of_isHomeomorph
    {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Set Y)
    (h : IsHomeomorph (U.restrictPreimage f)) :
    W (AlgebraicTopology.subspaceMap f
      (fun _ hx => hx : Set.MapsTo f (f ⁻¹' U) U)) := by
  let e := IsHomeomorph.homeomorph (U.restrictPreimage f) h
  exact TopCat.mem_of_eq_toFun e.toHomotopyEquiv rfl

private theorem cubeCellRestriction_mem_W {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    W (AlgebraicTopology.subspaceMap c.k
      (fun _ hx => hx : Set.MapsTo c.k
        (c.k ⁻¹' oneCellCellOpen c.outerSquare)
        (oneCellCellOpen c.outerSquare))) := by
  have hj' : Topology.IsClosedEmbedding c.j'.hom :=
    isClosedEmbedding_simplexCell_oldLeg c.outerPushout.flip
  apply subspaceMap_preimage_mem_W_of_isHomeomorph
  exact TopCat.isHomeomorph_oneCellOpenComplement_restrictPreimage
    c.lowerPushout.flip hj'

private theorem cubeOverlapRestriction_mem_W {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    W (AlgebraicTopology.subspaceMap c.k
      (fun _ hx => hx : Set.MapsTo c.k
        (c.k ⁻¹' (oneCellOldOpen c.outerSquare ∩
          oneCellCellOpen c.outerSquare))
        (oneCellOldOpen c.outerSquare ∩
          oneCellCellOpen c.outerSquare))) := by
  let U := oneCellOldOpen c.outerSquare ∩ oneCellCellOpen c.outerSquare
  have hU : IsOpen U :=
    (oneCellOldOpen_isOpen c.outerSquare).inter
      (oneCellCellOpen_isOpen c.outerSquare)
  have hr : c.j' ⁻¹' U = ∅ := by
    ext x
    constructor
    · intro hx
      change c.j' x ∈ oneCellOldOpen c.outerSquare ∩
        oneCellCellOpen c.outerSquare at hx
      exact ((Set.mem_compl_iff _ _).mp hx.2) ⟨x, rfl⟩
    · intro hx
      exact hx.elim
  have hl : c.k ⁻¹' U ⊆ (Set.range c.upper.j.hom)ᶜ := by
    have hpre :=
      TopCat.preimage_oneCellOpenComplement_eq c.lowerPushout.flip
    change c.k ⁻¹' (Set.range c.j'.hom)ᶜ =
      (Set.range c.upper.j.hom)ᶜ at hpre
    intro x hx
    rw [← hpre]
    exact hx.2
  apply subspaceMap_preimage_mem_W_of_isHomeomorph
  exact TopCat.isHomeomorph_restrictPreimage_inr_of_isPushout
    c.lowerPushout.flip hU hr hl

private def twoOpenCover {X : TopCat.{u}}
    (A B : TopologicalSpace.Opens X) :
    Bool → TopologicalSpace.Opens X :=
  fun b => if b then A else B

private theorem twoOpenCover_isOpenCover {X : TopCat.{u}}
    (A B : TopologicalSpace.Opens X)
    (hcover : (Set.univ : Set X) ⊆ (A : Set X) ∪ (B : Set X)) :
    TopologicalSpace.IsOpenCover (twoOpenCover A B) := by
  apply TopologicalSpace.IsOpenCover.of_sets
    (fun b => (twoOpenCover A B b).isOpen)
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  rcases hcover (Set.mem_univ x) with hx | hx
  · exact ⟨true, by simpa [twoOpenCover] using hx⟩
  · exact ⟨false, by simpa [twoOpenCover] using hx⟩

private def cubeTargetOldOpen {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    TopologicalSpace.Opens c.Y' :=
  ⟨oneCellOldOpen c.outerSquare,
    oneCellOldOpen_isOpen c.outerSquare⟩

private def cubeTargetCellOpen {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    TopologicalSpace.Opens c.Y' :=
  ⟨oneCellCellOpen c.outerSquare,
    oneCellCellOpen_isOpen c.outerSquare⟩

private def cubeSourceOldOpen {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    TopologicalSpace.Opens c.upper.Y :=
  ⟨c.k ⁻¹' oneCellOldOpen c.outerSquare,
    (oneCellOldOpen_isOpen c.outerSquare).preimage c.k.hom.continuous⟩

private def cubeSourceCellOpen {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    TopologicalSpace.Opens c.upper.Y :=
  ⟨c.k ⁻¹' oneCellCellOpen c.outerSquare,
    (oneCellCellOpen_isOpen c.outerSquare).preimage c.k.hom.continuous⟩

private theorem cubeTargetOpenCover {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    TopologicalSpace.IsOpenCover
      (twoOpenCover (cubeTargetOldOpen c) (cubeTargetCellOpen c)) := by
  apply twoOpenCover_isOpenCover
  exact oneCellOpenCover c.outerSquare

private theorem cubeSourceOpenCover {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    TopologicalSpace.IsOpenCover
      (twoOpenCover (cubeSourceOldOpen c) (cubeSourceCellOpen c)) := by
  apply twoOpenCover_isOpenCover
  intro y _hy
  have hy := oneCellOpenCover c.outerSquare (Set.mem_univ (c.k y))
  exact hy

private theorem cubeOldRestriction_mem_W {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) (hh : W c.h) :
    W (AlgebraicTopology.subspaceMap c.k
      (fun _ hx => hx : Set.MapsTo c.k
        (c.k ⁻¹' oneCellOldOpen c.outerSquare)
        (oneCellOldOpen c.outerSquare))) := by
  change W (cubeLowerOldRestriction c).rU
  exact cubeLowerOld_right_mem_W c hh

private theorem subordinateSup_ι_mem_realizationWeakEquivalences
    {X : TopCat.{u}} (A B : TopologicalSpace.Opens X)
    (hcover : TopologicalSpace.IsOpenCover (twoOpenCover A B)) :
    SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateSet (A : Set X) ⊔
        AlgebraicTopology.subordinateSet (B : Set X)).ι := by
  have hBoth : SSet.realizationWeakEquivalences
      (AlgebraicTopology.subCxBoth (A : Set X) (B : Set X)).ι := by
    have h :=
      AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences
        (twoOpenCover A B) hcover
    have hCover :
        (fun b => ((twoOpenCover A B b : TopologicalSpace.Opens X) : Set X)) =
          AlgebraicTopology.smallCoverBoth (A : Set X) (B : Set X) := by
      funext b
      cases b <;> rfl
    change SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateCover
        (fun b => ((twoOpenCover A B b : TopologicalSpace.Opens X) : Set X))).ι at h
    rw [hCover] at h
    exact h
  let e := subordinateTwoCoverIso (A : Set X) (B : Set X)
  have hcomp : SSet.realizationWeakEquivalences
      (e.hom ≫ (AlgebraicTopology.subCxBoth
        (A : Set X) (B : Set X)).ι) :=
    SSet.realizationWeakEquivalences.comp_mem _ _
      (SSet.realizationWeakEquivalences.of_isIso e.hom) hBoth
  have heq : e.hom ≫ (AlgebraicTopology.subCxBoth
      (A : Set X) (B : Set X)).ι =
        (AlgebraicTopology.subordinateSet (A : Set X) ⊔
          AlgebraicTopology.subordinateSet (B : Set X)).ι := by
    apply (cancel_mono (TopCat.toSSet.map (𝟙 X))).mp
    simp [e, subordinateTwoCoverIso]
  rw [heq] at hcomp
  exact hcomp

private theorem cubeOverlapForMapsTo_mem_W {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) :
    let hA : Set.MapsTo c.k
        (c.k ⁻¹' oneCellOldOpen c.outerSquare)
        (oneCellOldOpen c.outerSquare) := fun _ hx => hx
    let hB : Set.MapsTo c.k
        (c.k ⁻¹' oneCellCellOpen c.outerSquare)
        (oneCellCellOpen c.outerSquare) := fun _ hx => hx
    W (AlgebraicTopology.subspaceMap c.k (mapsToInter c.k hA hB)) := by
  dsimp only
  let hA : Set.MapsTo c.k
      (c.k ⁻¹' oneCellOldOpen c.outerSquare)
      (oneCellOldOpen c.outerSquare) := fun _ hx => hx
  let hB : Set.MapsTo c.k
      (c.k ⁻¹' oneCellCellOpen c.outerSquare)
      (oneCellCellOpen c.outerSquare) := fun _ hx => hx
  let hI : Set.MapsTo c.k
      ((c.k ⁻¹' oneCellOldOpen c.outerSquare) ∩
        (c.k ⁻¹' oneCellCellOpen c.outerSquare))
      (oneCellOldOpen c.outerSquare ∩
        oneCellCellOpen c.outerSquare) := mapsToInter c.k hA hB
  let hRaw : Set.MapsTo c.k
      (c.k ⁻¹' (oneCellOldOpen c.outerSquare ∩
        oneCellCellOpen c.outerSquare))
      (oneCellOldOpen c.outerSquare ∩
        oneCellCellOpen c.outerSquare) := fun _ hx => hx
  have hDom :
      (c.k ⁻¹' oneCellOldOpen c.outerSquare) ∩
          (c.k ⁻¹' oneCellCellOpen c.outerSquare) =
        c.k ⁻¹' (oneCellOldOpen c.outerSquare ∩
          oneCellCellOpen c.outerSquare) := by
    ext x
    rfl
  let e₁ : TopCat.of ↥((c.k ⁻¹' oneCellOldOpen c.outerSquare) ∩
        (c.k ⁻¹' oneCellCellOpen c.outerSquare)) ≅
      TopCat.of ↥(c.k ⁻¹' (oneCellOldOpen c.outerSquare ∩
        oneCellCellOpen c.outerSquare)) :=
    TopCat.isoOfHomeo (Homeomorph.setCongr hDom)
  let e₂ : TopCat.of ↥(oneCellOldOpen c.outerSquare ∩
      oneCellCellOpen c.outerSquare) ≅
      TopCat.of ↥(oneCellOldOpen c.outerSquare ∩
        oneCellCellOpen c.outerSquare) :=
    Iso.refl _
  have hcomm : e₁.hom ≫ AlgebraicTopology.subspaceMap c.k hRaw =
      AlgebraicTopology.subspaceMap c.k hI ≫ e₂.hom := by
    apply TopCat.hom_ext
    ext x
    rfl
  let e : Arrow.mk (AlgebraicTopology.subspaceMap c.k hI) ≅
      Arrow.mk (AlgebraicTopology.subspaceMap c.k hRaw) :=
    Arrow.isoMk e₁ e₂ hcomm
  exact (W.arrow_mk_iso_iff e).2 (cubeOverlapRestriction_mem_W c)

private theorem cubeSubordinateSupMap_mem_realizationWeakEquivalences
    {n : ℕ} (c : BoundaryOneCellAttachmentCube.{u} n) (hh : W c.h) :
    let hA : Set.MapsTo c.k
        (c.k ⁻¹' oneCellOldOpen c.outerSquare)
        (oneCellOldOpen c.outerSquare) := fun _ hx => hx
    let hB : Set.MapsTo c.k
        (c.k ⁻¹' oneCellCellOpen c.outerSquare)
        (oneCellCellOpen c.outerSquare) := fun _ hx => hx
    SSet.realizationWeakEquivalences (subordinateSupMap c.k hA hB) := by
  dsimp only
  let hA : Set.MapsTo c.k
      (c.k ⁻¹' oneCellOldOpen c.outerSquare)
      (oneCellOldOpen c.outerSquare) := fun _ hx => hx
  let hB : Set.MapsTo c.k
      (c.k ⁻¹' oneCellCellOpen c.outerSquare)
      (oneCellCellOpen c.outerSquare) := fun _ hx => hx
  apply subordinateSupMap_mem_realizationWeakEquivalences c.k hA hB
  · simpa only [AlgebraicTopology.subspaceMap_proof_irrel] using
      cubeOldRestriction_mem_W c hh
  · simpa only [AlgebraicTopology.subspaceMap_proof_irrel] using
      cubeCellRestriction_mem_W c
  · simpa only [AlgebraicTopology.subspaceMap_proof_irrel] using
      cubeOverlapForMapsTo_mem_W c

private theorem positiveBoundaryCubeGluing {n : ℕ}
    (c : BoundaryOneCellAttachmentCube.{u} n) (_hn : 0 < n)
    (hh : W c.h) : W c.k := by
  let A : TopologicalSpace.Opens c.upper.Y := cubeSourceOldOpen c
  let B : TopologicalSpace.Opens c.upper.Y := cubeSourceCellOpen c
  let A' : TopologicalSpace.Opens c.Y' := cubeTargetOldOpen c
  let B' : TopologicalSpace.Opens c.Y' := cubeTargetCellOpen c
  let hA : Set.MapsTo c.k (A : Set c.upper.Y) (A' : Set c.Y') :=
    fun _ hx => hx
  let hB : Set.MapsTo c.k (B : Set c.upper.Y) (B' : Set c.Y') :=
    fun _ hx => hx
  let d := subordinateSupMap c.k hA hB
  have hd : SSet.realizationWeakEquivalences d := by
    change SSet.realizationWeakEquivalences
      (subordinateSupMap c.k
        (fun _ hx => hx : Set.MapsTo c.k
          (c.k ⁻¹' oneCellOldOpen c.outerSquare)
          (oneCellOldOpen c.outerSquare))
        (fun _ hx => hx : Set.MapsTo c.k
          (c.k ⁻¹' oneCellCellOpen c.outerSquare)
          (oneCellCellOpen c.outerSquare)))
    exact cubeSubordinateSupMap_mem_realizationWeakEquivalences c hh
  have hSource : SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateSet (A : Set c.upper.Y) ⊔
        AlgebraicTopology.subordinateSet (B : Set c.upper.Y)).ι :=
    subordinateSup_ι_mem_realizationWeakEquivalences A B
      (cubeSourceOpenCover c)
  have hTarget : SSet.realizationWeakEquivalences
      (AlgebraicTopology.subordinateSet (A' : Set c.Y') ⊔
        AlgebraicTopology.subordinateSet (B' : Set c.Y')).ι :=
    subordinateSup_ι_mem_realizationWeakEquivalences A' B'
      (cubeTargetOpenCover c)
  have hcomp : SSet.realizationWeakEquivalences
      ((AlgebraicTopology.subordinateSet (A : Set c.upper.Y) ⊔
          AlgebraicTopology.subordinateSet (B : Set c.upper.Y)).ι ≫
        TopCat.toSSet.map c.k) := by
    have hdt : SSet.realizationWeakEquivalences
        (d ≫ (AlgebraicTopology.subordinateSet (A' : Set c.Y') ⊔
          AlgebraicTopology.subordinateSet (B' : Set c.Y')).ι) :=
      SSet.realizationWeakEquivalences.comp_mem _ _ hd hTarget
    rw [subordinateSupMap_ι] at hdt
    exact hdt
  have hkSing : SSet.realizationWeakEquivalences (TopCat.toSSet.map c.k) :=
    SSet.realizationWeakEquivalences.of_precomp _ _ hSource hcomp
  let _ : SSet.KanComplex (TopCat.toSSet.obj c.upper.Y) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj c.Y') :=
    TopCat.toSSet_obj_kanComplex _
  change TopCat.weakHomotopyEquivalences c.k
  rw [TopCat.mem_weakHomotopyEquivalences_iff]
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr hkSing

private theorem boundaryPushouts_le_Q :
    (I.{u} : MorphismProperty TopCat.{u}).pushouts ≤ Q := by
  intro X Y j hj
  obtain ⟨A, B, i, f, g, hi, hupper⟩ := hj
  change TopCat.realizedBoundaryInclusions i at hi
  unfold TopCat.realizedBoundaryInclusions at hi
  rw [MorphismProperty.ofHoms_iff] at hi
  obtain ⟨n, hn⟩ := hi
  cases hn
  change W.IsStableUnderCobaseChangeAlong j
  refine { of_isPushout := ?_ }
  intro Z W' f' g' h hlower hh
  let c : BoundaryOneCellAttachmentCube.{u} n :=
    { upper :=
        { X := X
          Y := Y
          f := f
          f' := g
          j := j
          isPushout := hupper.flip }
      X' := Z
      Y' := W'
      h := h
      j' := f'
      k := g'
      lowerPushout := hlower }
  rcases n with _ | n
  · exact boundaryZeroCubeGluing c hh
  · exact positiveBoundaryCubeGluing c (Nat.succ_pos n) hh

private theorem selectedTopCatIsLeftProper :
    IsLeftProper TopCat.{u} :=
  selectedIsLeftProperOfBoundaryPushouts boundaryPushouts_le_Q



end TopCatLeftProperProof

namespace TopCat.modelCategory

/-- The selected all-universe TopCat model structure is left proper. -/
noncomputable scoped instance instIsLeftProper :
    HomotopicalAlgebra.IsLeftProper TopCat.{u} :=
  TopCatLeftProperProof.selectedTopCatIsLeftProper

end TopCat.modelCategory
