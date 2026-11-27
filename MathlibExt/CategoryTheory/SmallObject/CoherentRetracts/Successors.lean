/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.PrefixGlue
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.SuccessorGeometry
public import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc

/-!
# Complete original successor prefixes

An original source-stage Arrow retract constructs the next complete prefix
by its two genuine pushouts. The whole original source functor, exact old
restriction, bottom splitting, successor memberships and every old limit
cocone witness are retained. No next-prefix outcome is supplied.

The actual full extension and functor-projection equations supplement the
pinned SmallObject successor API used by this construction. This implements
the coherent successor step in Hovey, Model Categories, Proposition 2.1.16,
printed pp.33–34, for an arbitrary original morphism class.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

namespace CategoryTheory.SmallObject.SuccStruct

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [SuccOrder J] {gamma : J} (hgamma : ¬IsMax gamma)
  (D : Set.Iic gamma ⥤ C) {X : C} (t : D.obj ⟨gamma, le_rfl⟩ ⟶ X)

/-- The whole old prefix of a successor extension is exactly the supplied original prefix. -/
theorem extendToSucc_restrict_eq :
    SmallObject.restrictionLE (extendToSucc hgamma D t) (Order.le_succ gamma) = D :=
  Functor.ext_of_iso (extendToSuccRestrictionLEIso hgamma D t)
    (fun i => extendToSucc_obj_eq hgamma D t i.1 i.2) (by intro i; rfl)

/-- Functorial projection retains the actual successor point and its complete supplied map. -/
theorem extendToSucc_comp {E : Type u'} [Category.{v'} E] (H : C ⥤ E) :
    extendToSucc hgamma D t ⋙ H = extendToSucc hgamma (D ⋙ H) (H.map t) := by
  apply Functor.hext
  · intro i
    dsimp only [Functor.comp_obj, extendToSucc, extendToSucc.obj]
    split_ifs <;> rfl
  · intro i j f
    by_cases hj : j.1 ≤ gamma
    · simp only [Functor.comp_map, extendToSucc, extendToSucc.map, dite_eq_left hj,
        extendToSucc.objIso, eqToIso.hom, eqToIso.inv,
        Functor.map_comp, eqToHom_map]
      simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
        heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
      rfl
    · by_cases hi : i.1 ≤ gamma
      · simp only [Functor.comp_map, extendToSucc, extendToSucc.map,
          dite_eq_right hj, dite_eq_left hi, extendToSucc.objIso,
          extendToSucc.objSuccIso, eqToIso.hom, eqToIso.inv,
          Functor.map_comp, eqToHom_map]
        simp only [eqToHom_trans, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
        simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
        rfl
      · obtain rfl : i = (⟨Order.succ gamma, by simp⟩ : Set.Iic (Order.succ gamma)) :=
          Subtype.ext (le_antisymm i.2 (Order.succ_le_of_lt (not_le.1 hi)))
        obtain rfl : j = (⟨Order.succ gamma, by simp⟩ : Set.Iic (Order.succ gamma)) :=
          Subtype.ext (le_antisymm j.2 (Order.succ_le_of_lt (not_le.1 hj)))
        obtain rfl : f = 𝟙 (⟨Order.succ gamma, by simp⟩ : Set.Iic (Order.succ gamma)) :=
          Subsingleton.elim _ _
        rw [(extendToSucc hgamma D t ⋙ H).map_id _,
          (extendToSucc hgamma (D ⋙ H) (H.map t)).map_id _]
        congr 1
        dsimp only [Functor.comp_obj, extendToSucc, extendToSucc.obj]
        split_ifs <;> rfl

/-- Equality of the original prefix transports only the source of the actual original successor
map. -/
theorem extendToSucc_precompose_eq {D' : Set.Iic gamma ⥤ C} (e : D = D')
    {X' : C} (t' : D'.obj ⟨gamma, le_rfl⟩ ⟶ X') :
    extendToSucc hgamma D (eqToHom (Functor.congr_obj e ⟨gamma, le_rfl⟩) ≫ t') =
      extendToSucc hgamma D' t' := by
  cases e
  simp only [eqToHom_refl, Category.id_comp]

/-- Extending by the actual original successor arrow retains the whole original next prefix. -/
theorem extendToSucc_original_eq (F : J ⥤ C) :
    extendToSucc hgamma ((Set.initialSegIic gamma).monotone.functor ⋙ F)
        (F.map (homOfLE (Order.le_succ gamma))) =
      (Set.initialSegIic (Order.succ gamma)).monotone.functor ⋙ F := by
  apply Functor.hext
  · intro i
    by_cases hi : i.1 ≤ gamma
    · exact extendToSucc_obj_eq hgamma _ _ i.1 hi
    · obtain rfl : i = (⟨Order.succ gamma, by simp⟩ : Set.Iic (Order.succ gamma)) :=
        Subtype.ext (le_antisymm i.2 (Order.succ_le_of_lt (not_le.1 hi)))
      exact extendToSucc_obj_succ_eq hgamma _ _
  · intro i j f
    by_cases hj : j.1 ≤ gamma
    · exact (conj_eqToHom_iff_heq _ _
        (extendToSucc_obj_eq hgamma _ _ i.1
          ((show i.1 ≤ j.1 from leOfHom f).trans hj))
        (extendToSucc_obj_eq hgamma _ _ j.1 hj)).mp
          (extendToSucc_map hgamma ((Set.initialSegIic gamma).monotone.functor ⋙ F)
            (F.map (homOfLE (Order.le_succ gamma))) i.1 j.1 (leOfHom f) hj)
    · obtain rfl : j = (⟨Order.succ gamma, by simp⟩ : Set.Iic (Order.succ gamma)) :=
        Subtype.ext (le_antisymm j.2 (Order.succ_le_of_lt (not_le.1 hj)))
      by_cases hi : i.1 ≤ gamma
      · simp only [Functor.comp_map, extendToSucc, extendToSucc.map,
          dite_eq_right (show ¬Order.succ gamma ≤ gamma by
            simpa only [Order.succ_le_iff_isMax] using hgamma), dite_eq_left hi,
          extendToSucc.objIso, extendToSucc.objSuccIso, eqToIso.hom, eqToIso.inv]
        simp only [eqToHom_trans, eqToHom_comp_heq_iff]
        simp only [← Category.assoc, comp_eqToHom_heq_iff]
        change F.map (homOfLE hi) ≫ F.map (homOfLE (Order.le_succ gamma)) ≍
          F.map (homOfLE (hi.trans (Order.le_succ gamma)))
        rw [← F.map_comp]
        rfl
      · obtain rfl : i = (⟨Order.succ gamma, by simp⟩ : Set.Iic (Order.succ gamma)) :=
          Subtype.ext (le_antisymm i.2 (Order.succ_le_of_lt (not_le.1 hi)))
        obtain rfl : f = 𝟙 (⟨Order.succ gamma, by simp⟩ : Set.Iic (Order.succ gamma)) :=
          Subsingleton.elim _ _
        rw [(extendToSucc hgamma ((Set.initialSegIic gamma).monotone.functor ⋙ F)
          (F.map (homOfLE (Order.le_succ gamma)))).map_id _,
          ((Set.initialSegIic (Order.succ gamma)).monotone.functor ⋙ F).map_id _]
        congr 1
        exact extendToSucc_obj_succ_eq hgamma
          ((Set.initialSegIic gamma).monotone.functor ⋙ F)
          (F.map (homOfLE (Order.le_succ gamma)))

end CategoryTheory.SmallObject.SuccStruct

namespace CategoryTheory.SmallObject.CoherentRetracts.PrefixSplitSuccessor
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C) (gamma : J) (S : PrefixSplit P F gamma)

/-- The actual source successor uses the original F map and the proved original source equality. -/
def sourceMap : (S.D.obj ⟨gamma, le_rfl⟩).source ⟶ F.obj (Order.succ gamma) :=
  eqToHom (Functor.congr_obj S.source_eq ⟨gamma, le_rfl⟩) ≫
    F.map (homOfLE (Order.le_succ gamma))

variable (hgamma : ¬IsMax gamma) {A B : C} (k : A ⟶ B)
  (R : RetractArrow (sourceMap P F gamma S) k) [HasPushouts C]

/-- The same actual stage retract and the two genuine pushouts construct the next split map. -/
def nextMap : S.D.obj ⟨gamma, le_rfl⟩ ⟶
    SplitObject.successorObject (S.D.obj ⟨gamma, le_rfl⟩)
      (sourceMap P F gamma S) (ArrowRetractRootNormalization.root R)
      (ArrowRetractRootNormalization.arrowRetract R) (by rfl) :=
  SplitObject.successorMap (S.D.obj ⟨gamma, le_rfl⟩)
    (sourceMap P F gamma S) (ArrowRetractRootNormalization.root R)
    (ArrowRetractRootNormalization.arrowRetract R) (by rfl)

/-- Membership follows from the actual two pushout squares, without closure of P. -/
theorem nextMap_mem (hk : P k) : P.pushouts (nextMap P F gamma S k R).right :=
  SplitObject.originalSuccessor_mem P (S.D.obj ⟨gamma, le_rfl⟩)
    (sourceMap P F gamma S) k R hk

/-- Extend the original closed prefix using its actual constructed successor map. -/
def successorDiagram : Set.Iic (Order.succ gamma) ⥤ SplitObject C :=
  extendToSucc hgamma S.D (nextMap P F gamma S k R)

/-- The entire source functor retains every original source point and Hom value. -/
theorem successorDiagram_source :
    successorDiagram P F gamma S hgamma k R ⋙ SplitObject.sourceFunctor =
      (Set.initialSegIic (Order.succ gamma)).monotone.functor ⋙ F := by
  rw [successorDiagram, extendToSucc_comp]
  change extendToSucc hgamma (S.D ⋙ SplitObject.sourceFunctor) (sourceMap P F gamma S) = _
  exact (extendToSucc_precompose_eq hgamma (S.D ⋙ SplitObject.sourceFunctor)
    S.source_eq (F.map (homOfLE (Order.le_succ gamma)))).trans (extendToSucc_original_eq hgamma F)

/-- The whole old prefix, including all actual morphisms, is recovered literally. -/
theorem successorDiagram_restrict :
    SmallObject.restrictionLE (successorDiagram P F gamma S hgamma k R)
      (Order.le_succ gamma) = S.D :=
  extendToSucc_restrict_eq hgamma S.D (nextMap P F gamma S k R)

/-- The original bottom remains the exact identity splitting. -/
theorem successorDiagram_bottom :
    (successorDiagram P F gamma S hgamma k R).obj ⟨⊥, bot_le⟩ =
      SplitObject.identityObject (F.obj ⊥) :=
  (Functor.congr_obj (successorDiagram_restrict P F gamma S hgamma k R)
    (⟨⊥, bot_le⟩ : Set.Iic gamma)).trans S.bottom_eq

/-- Every actual successor is either the old prefix map or the newly constructed two-pushout map. -/
theorem successorDiagram_map_mem (hk : P k) (i : J) (hi : i < Order.succ gamma) :
    P.pushouts (((successorDiagram P F gamma S hgamma k R).map
      (homOfLE (Order.le_succ i) :
        ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)).right) := by
  have hig : i ≤ gamma := (Order.lt_succ_iff_of_not_isMax hgamma).1 hi
  obtain hi | rfl := hig.lt_or_eq
  · have hT := congrArg (fun G : Set.Iic gamma ⥤ SplitObject C =>
      G ⋙ SplitObject.targetFunctor) (successorDiagram_restrict P F gamma S hgamma k R)
    exact P.pushouts.of_eq (S.map_mem i hi)
      (Functor.congr_obj hT (⟨i, hi.le⟩ : Set.Iic gamma)).symm
      (Functor.congr_obj hT (⟨Order.succ i, Order.succ_le_of_lt hi⟩ : Set.Iic gamma)).symm
      (Functor.congr_hom hT (homOfLE (Order.le_succ i) :
        (⟨i, hi.le⟩ : Set.Iic gamma) ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩))
  · have hA : Arrow.mk (((successorDiagram P F i S hgamma k R).map
        (homOfLE (Order.le_succ i) :
          (⟨i, Order.le_succ i⟩ : Set.Iic (Order.succ i)) ⟶
            ⟨Order.succ i, le_rfl⟩)).right) = Arrow.mk (nextMap P F i S k R).right :=
      congrArg (fun a : Arrow (SplitObject C) => SplitObject.targetFunctor.mapArrow.obj a)
        (arrowSucc_extendToSucc hgamma S.D (nextMap P F i S k R))
    rw [← P.pushouts.arrow_mk_mem_toSet_iff, hA, P.pushouts.arrow_mk_mem_toSet_iff]
    exact nextMap_mem P F i S k R hk

/-- All genuine limits in the successor prefix are original old limits with their original target
UP. -/
theorem successorDiagram_continuous (i : J) (hi : Order.IsSuccLimit i)
    (his : i ≤ Order.succ gamma) :
    Nonempty (IsColimit (SmallObject.coconeOfLE
      (successorDiagram P F gamma S hgamma k R ⋙ SplitObject.targetFunctor) his)) := by
  have higamma : i ≤ gamma := (Order.IsSuccLimit.le_succ_iff hi).1 his
  have hT := congrArg (fun G : Set.Iic gamma ⥤ SplitObject C =>
    G ⋙ SplitObject.targetFunctor) (successorDiagram_restrict P F gamma S hgamma k R)
  change SmallObject.restrictionLE (successorDiagram P F gamma S hgamma k R ⋙
    SplitObject.targetFunctor) (Order.le_succ gamma) = S.D ⋙ SplitObject.targetFunctor at hT
  change Nonempty (IsColimit (SmallObject.coconeOfLE
    (SmallObject.restrictionLE (successorDiagram P F gamma S hgamma k R ⋙
      SplitObject.targetFunctor) (Order.le_succ gamma)) higamma))
  rw [hT]
  exact S.continuous i hi higamma

/-- The original stage retract produces the complete next prefix with no next-state outcome
input. -/
def successorState (hk : P k) : PrefixSplit P F (Order.succ gamma) where
  D := successorDiagram P F gamma S hgamma k R
  source_eq := successorDiagram_source P F gamma S hgamma k R
  bottom_eq := successorDiagram_bottom P F gamma S hgamma k R
  map_mem := successorDiagram_map_mem P F gamma S hgamma k R hk
  continuous := successorDiagram_continuous P F gamma S hgamma k R

/-- The complete constructed next state restricts literally to the same original prefix. -/
theorem successorState_restrict (hk : P k) :
    (successorState P F gamma S hgamma k R hk).restrict (Order.le_succ gamma) = S := by
  apply PrefixSplit.ext
  exact successorDiagram_restrict P F gamma S hgamma k R


/-- The source comparison is the actual original prefix source equality and identity target. -/
def originalSourceArrowIso : Arrow.mk (sourceMap P F gamma S) ≅
    Arrow.mk (F.map (homOfLE (Order.le_succ gamma))) :=
  Arrow.isoMk (eqToIso (Functor.congr_obj S.source_eq ⟨gamma, le_rfl⟩)) (Iso.refl _)
    (by
      change sourceMap P F gamma S = sourceMap P F gamma S ≫ 𝟙 (F.obj (Order.succ gamma))
      exact (Category.comp_id (sourceMap P F gamma S)).symm)

/-- The actual original source-stage retract transports through its original source equality. -/
def transportOriginalRetract
    (R0 : RetractArrow (F.map (homOfLE (Order.le_succ gamma))) k) :
    RetractArrow (sourceMap P F gamma S) k :=
  (Retract.ofIso (originalSourceArrowIso P F gamma S)).trans R0

/-- An actual original stage Arrow retract constructs a full successor state with the exact old
restriction. -/
def originalSuccessorState
    (R0 : RetractArrow (F.map (homOfLE (Order.le_succ gamma))) k) (hk : P k) :
    PrefixSplit P F (Order.succ gamma) :=
  successorState P F gamma S hgamma k (transportOriginalRetract P F gamma S k R0) hk

/-- The actual original-stage constructor recovers the full original old prefix. -/
theorem originalSuccessorState_restrict
    (R0 : RetractArrow (F.map (homOfLE (Order.le_succ gamma))) k) (hk : P k) :
    (originalSuccessorState P F gamma S hgamma k R0 hk).restrict (Order.le_succ gamma) = S :=
  successorState_restrict P F gamma S hgamma k (transportOriginalRetract P F gamma S k R0) hk


end
end CategoryTheory.SmallObject.CoherentRetracts.PrefixSplitSuccessor
