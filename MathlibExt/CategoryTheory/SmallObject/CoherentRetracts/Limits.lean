/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.PrefixGlue
public import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone

/-!
# Complete original limit prefixes

The particular original source cocone and its universal property, together
with the actual preceding target colimit, construct the complete limit
prefix. The source point, whole original source diagram, old prefixes and
all splitting maps are retained. No completed limit prefix is supplied.

This is the coherent limit construction used in Hovey, Model Categories,
Proposition 2.1.16, printed pp.33–34, with an arbitrary original morphism class.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

namespace CategoryTheory.SmallObject.SuccStruct

variable {C : Type u} [Category.{v} C] {J : Type w} [LinearOrder J]
  {gamma : J} {D : Set.Iio gamma ⥤ C} (c : Cocone D)

/-- The actual cocone extension restricts to exactly the original preceding diagram. -/
theorem ofCocone_restrict_eq (delta : J) (h : delta < gamma) :
    SmallObject.restrictionLE (ofCocone c) h.le =
      (CategoryTheory.SmallObject.CoherentRetracts.PrefixSplitGlue.prefixInclusion
          (LowerSet.Iio gamma) ⟨delta, h⟩).monotone.functor ⋙ D := by
  apply Functor.hext
  · intro i
    exact ofCocone_obj_eq c i.1 (lt_of_le_of_lt i.2 h)
  · intro i j f
    exact (conj_eqToHom_iff_heq _ _
      (ofCocone_obj_eq c i.1 (lt_of_le_of_lt i.2 h))
      (ofCocone_obj_eq c j.1 (lt_of_le_of_lt j.2 h))).mp
        (ofCocone_map c i.1 j.1 (leOfHom f) (lt_of_le_of_lt j.2 h))

/-- Extending the original diagram's own preceding cocone retains its whole closed prefix. -/
theorem ofCocone_original_eq (F : J ⥤ C) (gamma : J) :
    ofCocone ((Set.principalSegIio gamma).cocone F) =
      (Set.initialSegIic gamma).monotone.functor ⋙ F := by
  apply Functor.hext
  · intro i
    by_cases hi : i.1 < gamma
    · exact ofCocone_obj_eq _ i.1 hi
    · obtain rfl : i = (⟨gamma, by simp⟩ : Set.Iic gamma) :=
        Subtype.ext (le_antisymm i.2 (le_of_not_gt hi))
      exact ofCocone_obj_eq_pt _
  · intro i j f
    by_cases hj : j.1 < gamma
    · exact (conj_eqToHom_iff_heq _ _
        (ofCocone_obj_eq _ i.1 (lt_of_le_of_lt (leOfHom f) hj))
        (ofCocone_obj_eq _ j.1 hj)).mp
          (ofCocone_map ((Set.principalSegIio gamma).cocone F) i.1 j.1
            (leOfHom f) hj)
    · obtain rfl : j = (⟨gamma, by simp⟩ : Set.Iic gamma) :=
        Subtype.ext (le_antisymm j.2 (le_of_not_gt hj))
      by_cases hi : i.1 < gamma
      · exact (conj_eqToHom_iff_heq _ _
          (ofCocone_obj_eq _ i.1 hi) (ofCocone_obj_eq_pt _)).mp
            (ofCocone_map_to_top ((Set.principalSegIio gamma).cocone F) i.1 hi)
      · obtain rfl : i = (⟨gamma, by simp⟩ : Set.Iic gamma) :=
          Subtype.ext (le_antisymm i.2 (le_of_not_gt hi))
        obtain rfl : f = 𝟙 (⟨gamma, by simp⟩ : Set.Iic gamma) := Subsingleton.elim _ _
        rw [(ofCocone ((Set.principalSegIio gamma).cocone F)).map_id _,
          ((Set.initialSegIic gamma).monotone.functor ⋙ F).map_id _]
        congr 1
        exact ofCocone_obj_eq_pt ((Set.principalSegIio gamma).cocone F)

private theorem map_heq {E : Type u'} [Category.{v'} E] (H : C ⥤ E)
    {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : f ≍ g) : H.map f ≍ H.map g := by
  cases hA
  cases hB
  exact heq_of_eq (congrArg (fun z => H.map z) (eq_of_heq h))

/-- A functor keeps the complete cocone extension, with the actual mapped point and legs. -/
theorem ofCocone_comp {E : Type u'} [Category.{v'} E] (H : C ⥤ E) :
    ofCocone c ⋙ H = ofCocone (H.mapCocone c) := by
  apply Functor.hext
  · intro i
    dsimp only [Functor.comp_obj, ofCocone, ofCocone.obj]
    split_ifs <;> rfl
  · intro i j f
    by_cases hj : j.1 < gamma
    · have hi : i.1 < gamma := (show i.1 ≤ j.1 from leOfHom f).trans_lt hj
      have hOld := (conj_eqToHom_iff_heq _ _
        (ofCocone_obj_eq c i.1 hi) (ofCocone_obj_eq c j.1 hj)).mp
        (ofCocone_map c i.1 j.1 (leOfHom f) hj)
      have hNew := (conj_eqToHom_iff_heq _ _
        (ofCocone_obj_eq (H.mapCocone c) i.1 hi)
        (ofCocone_obj_eq (H.mapCocone c) j.1 hj)).mp
        (ofCocone_map (H.mapCocone c) i.1 j.1 (leOfHom f) hj)
      exact (map_heq H (ofCocone_obj_eq c i.1 hi) (ofCocone_obj_eq c j.1 hj) hOld).trans hNew.symm
    · obtain rfl : j = (⟨gamma, by simp⟩ : Set.Iic gamma) :=
        Subtype.ext (le_antisymm j.2 (le_of_not_gt hj))
      by_cases hi : i.1 < gamma
      · have hOld := (conj_eqToHom_iff_heq _ _
          (ofCocone_obj_eq c i.1 hi) (ofCocone_obj_eq_pt c)).mp
          (ofCocone_map_to_top c i.1 hi)
        have hNew := (conj_eqToHom_iff_heq _ _
          (ofCocone_obj_eq (H.mapCocone c) i.1 hi)
          (ofCocone_obj_eq_pt (H.mapCocone c))).mp
          (ofCocone_map_to_top (H.mapCocone c) i.1 hi)
        exact (map_heq H (ofCocone_obj_eq c i.1 hi) (ofCocone_obj_eq_pt c) hOld).trans hNew.symm
      · obtain rfl : i = (⟨gamma, by simp⟩ : Set.Iic gamma) :=
          Subtype.ext (le_antisymm i.2 (le_of_not_gt hi))
        obtain rfl : f = 𝟙 (⟨gamma, by simp⟩ : Set.Iic gamma) := Subsingleton.elim _ _
        rw [(ofCocone c ⋙ H).map_id _, (ofCocone (H.mapCocone c)).map_id _]
        congr 1
        dsimp only [Functor.comp_obj, ofCocone, ofCocone.obj]
        split_ifs <;> rfl

/-- Transport by an actual equality of preceding diagrams leaves the entire extension unchanged. -/
theorem ofCocone_precompose_eq {D' : Set.Iio gamma ⥤ C} (e : D = D') (c' : Cocone D') :
    ofCocone ((Cocone.precompose (eqToHom e)).obj c') = ofCocone c' := by
  cases e
  change ofCocone { pt := c'.pt, ι := (𝟙 D) ≫ c'.ι } = ofCocone c'
  rw [Category.id_comp]

end CategoryTheory.SmallObject.SuccStruct

namespace CategoryTheory.SmallObject.CoherentRetracts.PrefixSplitLimit
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct
open PrefixSplitGlue
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C) (gamma : J)
  (x : ((Set.principalSegIio gamma).monotone.functor.op ⋙ prefixSplitFunctor P F).sections)

/-- The actual original source cocone keeps the original endpoint and every original leg. -/
def sourceCocone : Cocone (precedingDiagram P F gamma x ⋙ SplitObject.sourceFunctor) :=
  (Cocone.precompose (eqToHom (precedingDiagram_source P F gamma x))).obj
    ((Set.principalSegIio gamma).cocone F)

/-- Only the actual original source UP is used; no full source-continuity outcome is a premise. -/
def sourceIsColimit (hc : IsColimit ((Set.principalSegIio gamma).cocone F)) :
    IsColimit (sourceCocone P F gamma x) :=
  (IsColimit.precomposeHomEquiv (eqToIso (precedingDiagram_source P F gamma x))
    ((Set.principalSegIio gamma).cocone F)).symm hc

variable [HasColimitsOfShape (Set.Iio gamma) C]
  (hc : IsColimit ((Set.principalSegIio gamma).cocone F)) (hgamma : Order.IsSuccLimit gamma)

/-- The two-component colimit uses the same original source point and actual target colimit. -/
def limitCocone : Cocone (precedingDiagram P F gamma x) :=
  SplitObject.colimitCocone (precedingDiagram P F gamma x) (sourceCocone P F gamma x)
    (colimit.cocone (precedingDiagram P F gamma x ⋙ SplitObject.targetFunctor))
    (sourceIsColimit P F gamma x hc)
    (colimit.isColimit (precedingDiagram P F gamma x ⋙ SplitObject.targetFunctor))

/-- Extend the actual preceding diagram by its constructed splitting cocone. -/
def limitDiagram : Set.Iic gamma ⥤ SplitObject C := ofCocone (limitCocone P F gamma x hc)

/-- Every original source object and Hom value is retained at the limit extension. -/
theorem limitDiagram_source : limitDiagram P F gamma x hc ⋙ SplitObject.sourceFunctor =
    (Set.initialSegIic gamma).monotone.functor ⋙ F := by
  rw [limitDiagram, ofCocone_comp]
  change ofCocone (sourceCocone P F gamma x) = _
  exact (ofCocone_precompose_eq (precedingDiagram_source P F gamma x)
    ((Set.principalSegIio gamma).cocone F)).trans (ofCocone_original_eq F gamma)

/-- The target is the same preceding target diagram extended by its actual chosen colimit. -/
theorem limitDiagram_target : limitDiagram P F gamma x hc ⋙ SplitObject.targetFunctor =
    ofCocone (colimit.cocone (precedingDiagram P F gamma x ⋙ SplitObject.targetFunctor)) := by
  rw [limitDiagram, ofCocone_comp]
  rfl

/-- Every closed original predecessor prefix is retained as a whole functor. -/
theorem limitDiagram_restrict (delta : J) (hdelta : delta < gamma) :
    SmallObject.restrictionLE (limitDiagram P F gamma x hc) hdelta.le =
      (x.val (Opposite.op (⟨delta, hdelta⟩ : Set.Iio gamma))).D :=
  (ofCocone_restrict_eq (limitCocone P F gamma x hc) delta hdelta).trans
    (precedingDiagram_restrict P F gamma x delta hdelta)

include hgamma in
/-- The actual original bottom keeps its identity splitting. -/
theorem limitDiagram_bottom :
    (limitDiagram P F gamma x hc).obj ⟨⊥, bot_le⟩ = SplitObject.identityObject (F.obj ⊥) :=
  (Functor.congr_obj (limitDiagram_restrict P F gamma x hc ⊥ (Order.IsSuccLimit.bot_lt hgamma))
    (⟨⊥, bot_le⟩ : Set.Iic (⊥ : J))).trans
    (x.val (Opposite.op (⟨⊥, Order.IsSuccLimit.bot_lt hgamma⟩ : Set.Iio gamma))).bottom_eq

include hgamma in
/-- The original successor maps are detected in the exact larger original predecessor prefix. -/
theorem limitDiagram_map_mem (i : J) (hi : i < gamma) :
    P.pushouts (((limitDiagram P F gamma x hc).map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)).right) := by
  have hsucc : Order.succ i < gamma := (Order.IsSuccLimit.succ_lt_iff hgamma).2 hi
  have hD := limitDiagram_restrict P F gamma x hc (Order.succ i) hsucc
  have hT := congrArg (fun G : Set.Iic (Order.succ i) ⥤ SplitObject C =>
    G ⋙ SplitObject.targetFunctor) hD
  have hlt : i < Order.succ i := Order.lt_succ_of_not_isMax (not_isMax_of_lt hi)
  exact P.pushouts.of_eq
    ((x.val (Opposite.op (⟨Order.succ i, hsucc⟩ : Set.Iio gamma))).map_mem i hlt)
    (Functor.congr_obj hT (⟨i, Order.le_succ i⟩ : Set.Iic (Order.succ i))).symm
    (Functor.congr_obj hT (⟨Order.succ i, le_rfl⟩ : Set.Iic (Order.succ i))).symm
    (Functor.congr_hom hT (homOfLE (Order.le_succ i) :
      (⟨i, Order.le_succ i⟩ : Set.Iic (Order.succ i)) ⟶ ⟨Order.succ i, le_rfl⟩))

/-- All old target limit UPs survive, and the new target limit is its actual chosen colimit. -/
theorem limitDiagram_continuous (i : J) (hi : Order.IsSuccLimit i) (higamma : i ≤ gamma) :
    Nonempty (IsColimit (SmallObject.coconeOfLE
      (limitDiagram P F gamma x hc ⋙ SplitObject.targetFunctor) higamma)) := by
  obtain higamma | rfl := higamma.lt_or_eq
  · have hT := congrArg (fun G : Set.Iic i ⥤ SplitObject C => G ⋙ SplitObject.targetFunctor)
      (limitDiagram_restrict P F gamma x hc i higamma)
    change Nonempty (IsColimit (SmallObject.coconeOfLE
      (SmallObject.restrictionLE (limitDiagram P F gamma x hc ⋙
          SplitObject.targetFunctor) higamma.le)
      (le_refl i)))
    change SmallObject.restrictionLE (limitDiagram P F gamma x hc ⋙ SplitObject.targetFunctor)
      higamma.le = (x.val (Opposite.op (⟨i, higamma⟩ : Set.Iio gamma))).D ⋙
        SplitObject.targetFunctor at hT
    rw [hT]
    exact (x.val (Opposite.op (⟨i, higamma⟩ : Set.Iio gamma))).continuous i hi le_rfl
  · rw [limitDiagram_target]
    exact ⟨isColimitCoconeOfLEOfCocone
      (colimit.isColimit (precedingDiagram P F i x ⋙ SplitObject.targetFunctor))⟩

/-- Actual preceding source and target UPs construct the complete original limit prefix. -/
def limitState : PrefixSplit P F gamma where
  D := limitDiagram P F gamma x hc
  source_eq := limitDiagram_source P F gamma x hc
  bottom_eq := limitDiagram_bottom P F gamma x hc hgamma
  map_mem := limitDiagram_map_mem P F gamma x hc hgamma
  continuous := limitDiagram_continuous P F gamma x hc

/-- The constructed limit state recovers each original complete predecessor literally. -/
theorem limitState_restrict (delta : J) (hdelta : delta < gamma) :
    (limitState P F gamma x hc hgamma).restrict hdelta.le =
      x.val (Opposite.op (⟨delta, hdelta⟩ : Set.Iio gamma)) := by
  apply PrefixSplit.ext
  exact limitDiagram_restrict P F gamma x hc delta hdelta

/-- The actual original projective-system map exhibits the genuine complete limit lift. -/
theorem limitState_map (delta : J) (hdelta : delta < gamma) :
    (prefixSplitFunctor P F).map (homOfLE hdelta.le).op (limitState P F gamma x hc hgamma) =
      x.val (Opposite.op (⟨delta, hdelta⟩ : Set.Iio gamma)) :=
  limitState_restrict P F gamma x hc hgamma delta hdelta


end
end CategoryTheory.SmallObject.CoherentRetracts.PrefixSplitLimit
