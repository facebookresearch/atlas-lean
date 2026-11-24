/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Absorption
public import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition
public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.OriginalShapes

/-!
# Actual chosen cellular representatives in coherent absorption

The original supplied representative at each nonmaximal stage determines the
successor lift. The whole compatible family is constructed from the identity
seed, retaining the original chain and its actual colimit maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.SuccStruct

namespace CategoryTheory.Functor.WellOrderInductionData

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {H : Jᵒᵖ ⥤ Type z} (d : H.WellOrderInductionData) (v₀ : H.obj (Opposite.op ⊥))

/-- The constructed section follows the actual supplied successor operation. -/
theorem sectionsMk_val_op_succ (j : J) (hj : ¬ IsMax j) :
    (d.sectionsMk v₀).val (Opposite.op (Order.succ j)) =
      d.succ j hj ((d.sectionsMk v₀).val (Opposite.op j)) := by
  have h := (default : d.Extension v₀ (Order.succ j)).map_succ j
    (Order.lt_succ_of_not_isMax hj)
  simp only [homOfLE_refl, op_id, Functor.map_id, id_apply, homOfLE_leOfHom] at h
  have hc := Extension.compatibility
    (default : d.Extension v₀ (Order.succ j)) (default : d.Extension v₀ j) (Order.le_succ j)
  rw [hc] at h
  exact h

end CategoryTheory.Functor.WellOrderInductionData

namespace CategoryTheory.SmallObject.CoherentRetracts.ChosenStages

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C) [HasPushouts C]
  [HasColimitsOfSize.{w, w} C] [F.IsWellOrderContinuous]
  {A B : {j : J // ¬ IsMax j} → C}
  (k : ∀ i, A i ⟶ B i)
  (R : ∀ i, RetractArrow (F.map (homOfLE (Order.le_succ i.1))) (k i))
  (hk : ∀ i, P (k i))

/-- The actual given representatives, source retracts and original limit UPs determine the lifts. -/
def inductionData : (prefixSplitFunctor P F).WellOrderInductionData where
  succ j hj S := PrefixSplitSuccessor.originalSuccessorState P F j S hj
    (k ⟨j, hj⟩) (R ⟨j, hj⟩) (hk ⟨j, hj⟩)
  map_succ j hj S := PrefixSplitSuccessor.originalSuccessorState_restrict P F j S hj
    (k ⟨j, hj⟩) (R ⟨j, hj⟩) (hk ⟨j, hj⟩)
  lift j hj x := PrefixSplitLimit.limitState P F j x
    (F.isColimitOfIsWellOrderContinuous j hj) hj
  map_lift j hj x i hi := PrefixSplitLimit.limitState_map P F j x
    (F.isColimitOfIsWellOrderContinuous j hj) hj i hi

variable [WellFoundedLT J]

/-- The complete family is constructed from the original seed and the actual chosen lifts. -/
def chosenSection : (prefixSplitFunctor P F).sections :=
  (inductionData P F k R hk).sectionsMk (PrefixSplit.seed (P := P) (F := F))

/-- Each constructed successor is the state of that same original supplied representative. -/
theorem section_succ (j : J) (hj : ¬ IsMax j) :
    (chosenSection P F k R hk).val (Opposite.op (Order.succ j)) =
      PrefixSplitSuccessor.originalSuccessorState P F j
        ((chosenSection P F k R hk).val (Opposite.op j)) hj
        (k ⟨j, hj⟩) (R ⟨j, hj⟩) (hk ⟨j, hj⟩) :=
  Functor.WellOrderInductionData.sectionsMk_val_op_succ
    (inductionData P F k R hk) (PrefixSplit.seed (P := P) (F := F)) j hj

/-- The complete constructed splitting diagram on the same original order. -/
def chosenDiagram : J ⥤ SplitObject C :=
  PrefixSplitGlue.wholeDiagram P F (chosenSection P F k R hk)

/-- Its actual target diagram, with the original outer labels unchanged. -/
def targetDiagram : J ⥤ C := chosenDiagram P F k R hk ⋙ SplitObject.targetFunctor

/-- The whole-order successor is the arrow of that same given representative's two pushouts. -/
theorem targetDiagram_arrowSucc (j : J) (hj : ¬ IsMax j) :
    Arrow.mk ((targetDiagram P F k R hk).map (homOfLE (Order.le_succ j))) =
      Arrow.mk (PrefixSplitSuccessor.nextMap P F j
        ((chosenSection P F k R hk).val (Opposite.op j)) (k ⟨j, hj⟩)
        (PrefixSplitSuccessor.transportOriginalRetract P F j
          ((chosenSection P F k R hk).val (Opposite.op j)) (k ⟨j, hj⟩) (R ⟨j, hj⟩))).right := by
  let x := chosenSection P F k R hk
  let S := x.val (Opposite.op j)
  let f : (⟨j, Order.le_succ j⟩ : Set.Iic (Order.succ j)) ⟶ ⟨Order.succ j, le_rfl⟩ :=
    homOfLE (Order.le_succ j)
  have hD := (PrefixSplitGlue.wholeDiagram_restrict P F x (Order.succ j)).trans
    (congrArg PrefixSplit.D (section_succ P F k R hk j hj))
  have hA := congrArg (fun H : Set.Iic (Order.succ j) ⥤ SplitObject C =>
    SplitObject.targetFunctor.mapArrow.obj (H.mapArrow.obj (Arrow.mk f))) hD
  let R' := PrefixSplitSuccessor.transportOriginalRetract P F j S
    (k ⟨j, hj⟩) (R ⟨j, hj⟩)
  have hB := congrArg (fun a : Arrow (SplitObject C) => SplitObject.targetFunctor.mapArrow.obj a)
    (arrowSucc_extendToSucc hj S.D (PrefixSplitSuccessor.nextMap P F j S (k ⟨j, hj⟩) R'))
  exact hA.trans hB

end CategoryTheory.SmallObject.CoherentRetracts.ChosenStages

namespace CategoryTheory.SmallObject.CoherentRetracts

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  (P : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
  (outer : CategoryTheory.TransfiniteCompositionOfShape J f)
  (x : (prefixSplitFunctor P outer.F).sections)

/-- Endpoint data constructed from an original source cocone and a constructed prefix section. -/
structure EndpointOfSectionData where
  /-- The actual chosen target endpoint. -/
  target : C
  /-- Its arrow has the original source X. -/
  arrow : X ⟶ target
  /-- The complete same-original-order target presentation. -/
  presentation : P.pushouts.TransfiniteCompositionOfShape J arrow
  /-- Its whole functor is the actual glued target functor. -/
  targetDiagram_eq : presentation.F =
    PrefixSplitGlue.wholeDiagram P outer.F x ⋙ SplitObject.targetFunctor
  /-- The actual endpoint Arrow retract. -/
  retract : RetractArrow f arrow
  /-- The source inclusion is literally the original identity. -/
  inclusion_source : retract.i.left = 𝟙 X
  /-- The source retraction is literally the original identity. -/
  retraction_source : retract.r.left = 𝟙 X

variable [HasColimitsOfSize.{w, w} C]

/-- The actual original endpoint cocone, UP and factor construct all target and retract maps. -/
def endpointOfSection : EndpointOfSectionData P outer x := by
  let D := PrefixSplitGlue.wholeDiagram P outer.F x
  let G := D ⋙ SplitObject.targetFunctor
  have hSource : D ⋙ SplitObject.sourceFunctor = outer.F :=
    PrefixSplitGlue.wholeDiagram_source P outer.F x
  let cF : Cocone (D ⋙ SplitObject.sourceFunctor) :=
    (Cocone.precompose (eqToHom hSource)).obj (Cocone.mk Y outer.incl)
  let hF : IsColimit cF :=
    (IsColimit.precomposeHomEquiv (eqToIso hSource) (Cocone.mk Y outer.incl)).symm outer.isColimit
  let cG : Cocone G := colimit.cocone G
  let hG : IsColimit cG := colimit.isColimit G
  let i := SplitObject.inclusionNatTrans D
  let r := SplitObject.retractionNatTrans D
  let sF : X ⟶ (D ⋙ SplitObject.sourceFunctor).obj ⊥ :=
    outer.isoBot.inv ≫ eqToHom (Functor.congr_obj hSource (⊥ : J)).symm
  let sG : X ⟶ G.obj ⊥ := sF ≫ i.app ⊥
  let _ : IsIso (i.app ⊥) := by
    change IsIso (D.obj ⊥).inclusion
    dsimp only [D]
    rw [PrefixSplitGlue.wholeDiagram_bottom]
    change IsIso (𝟙 (outer.F.obj ⊥))
    infer_instance
  let _ : IsIso sF := by dsimp only [sF]; infer_instance
  let _ : IsIso sG := by dsimp only [sG]; infer_instance
  have hsR : sG ≫ r.app ⊥ = sF := by
    have hsplit : i.app ⊥ ≫ r.app ⊥ = 𝟙 ((D ⋙ SplitObject.sourceFunctor).obj ⊥) := by
      have h := congrArg (fun t => t.app (⊥ : J)) (SplitObject.inclusion_retraction D)
      exact h
    change (sF ≫ i.app ⊥) ≫ r.app ⊥ = sF
    exact (Category.assoc sF (i.app ⊥) (r.app ⊥)).trans
      ((congrArg (fun t => sF ≫ t) hsplit).trans (Category.comp_id sF))
  let g : X ⟶ cG.pt := sG ≫ cG.ι.app ⊥
  let d : P.pushouts.TransfiniteCompositionOfShape J g :=
    { F := G
      isoBot := (asIso sG).symm
      isWellOrderContinuous := (show G.IsWellOrderContinuous from {
        nonempty_isColimit := PrefixSplitGlue.wholeDiagram_continuous P outer.F x })
      incl := cG.ι
      isColimit := hG
      fac := rfl
      map_mem j hj := PrefixSplitGlue.wholeDiagram_map_mem P outer.F x j hj }
  let hRaw : RetractArrow (sF ≫ cF.ι.app ⊥) g :=
    retractArrowOfColimitCocones cF cG hF hG i r (SplitObject.inclusion_retraction D)
      (⊥ : J) sF sG rfl hsR
  have hleg : cF.ι.app ⊥ =
      eqToHom (Functor.congr_obj hSource (⊥ : J)) ≫ outer.incl.app ⊥ := by
    change (eqToHom hSource).app ⊥ ≫ outer.incl.app ⊥ = _
    rw [eqToHom_app]
  have hOriginal : sF ≫ cF.ι.app ⊥ = f := by
    rw [hleg]
    change (outer.isoBot.inv ≫ eqToHom (Functor.congr_obj hSource (⊥ : J)).symm) ≫
      (eqToHom (Functor.congr_obj hSource (⊥ : J)) ≫ outer.incl.app ⊥) = f
    rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact outer.fac
  let h : RetractArrow f g :=
    { i := Arrow.homMk (𝟙 X) hRaw.i.right (by
        change 𝟙 X ≫ g = f ≫ hRaw.i.right
        rw [← hOriginal]
        exact hRaw.i_w)
      r := Arrow.homMk (𝟙 X) hRaw.r.right (by
        change 𝟙 X ≫ f = g ≫ hRaw.r.right
        rw [← hOriginal]
        exact hRaw.r_w)
      retract := by
        ext
        · exact Category.id_comp _
        · exact hRaw.retract_right }
  exact ⟨cG.pt, g, d, rfl, h, rfl, rfl⟩

/-- The original whole source functor is included by the actual constructed splitting maps. -/
def inclusionOfSection : outer.F ⟶
    PrefixSplitGlue.wholeDiagram P outer.F x ⋙ SplitObject.targetFunctor :=
  eqToHom (PrefixSplitGlue.wholeDiagram_source P outer.F x).symm ≫
    SplitObject.inclusionNatTrans (PrefixSplitGlue.wholeDiagram P outer.F x)

/-- The original whole source functor is retracted by the actual constructed splitting maps. -/
def retractionOfSection :
    PrefixSplitGlue.wholeDiagram P outer.F x ⋙ SplitObject.targetFunctor ⟶ outer.F :=
  SplitObject.retractionNatTrans (PrefixSplitGlue.wholeDiagram P outer.F x) ≫
    eqToHom (PrefixSplitGlue.wholeDiagram_source P outer.F x)

omit [HasColimitsOfSize.{w, w} C] in
/-- Every original component of the natural splitting is retained. -/
theorem section_natural_splitting : inclusionOfSection P outer x ≫ retractionOfSection P outer x =
    𝟙 outer.F := by
  unfold inclusionOfSection retractionOfSection
  rw [Category.assoc, ← Category.assoc (SplitObject.inclusionNatTrans _),
    SplitObject.inclusion_retraction, Category.id_comp, eqToHom_trans, eqToHom_refl]

end CategoryTheory.SmallObject.CoherentRetracts

namespace CategoryTheory.SmallObject.CoherentRetracts.ChosenCellularStages

open CellularNormalization

universe w' ν
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (P : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
  (outer : CategoryTheory.TransfiniteCompositionOfShape J f)
  {A B : {j : J // ¬ IsMax j} → C}
  (k : ∀ i, A i ⟶ B i)
  (R : ∀ i, RetractArrow (outer.F.map (homOfLE (Order.le_succ i.1))) (k i))
  (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
  (c : ∀ i, (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
    (K i).carrier (k i))

local instance sourceContinuous : outer.F.IsWellOrderContinuous := outer.isWellOrderContinuous

omit [OrderBot J] [SuccOrder J] [WellFoundedLT J] [HasPushouts C]
  [HasColimitsOfSize.{w, w} C] in
include c in
/-- The supplied cellular history proves its representative belongs to that original class. -/
theorem representative_mem (i : {j : J // ¬ IsMax j}) :
    (MorphismProperty.transfiniteCompositions.{w'}
      (MorphismProperty.coproducts.{ν} P).pushouts) (k i) :=
  MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions
    (MorphismProperty.coproducts.{ν} P).pushouts (K i).carrier _ (c i).mem

/-- The complete family uses precisely the given original representatives and retracts. -/
def originalSection : (prefixSplitFunctor
    (MorphismProperty.transfiniteCompositions.{w'}
      (MorphismProperty.coproducts.{ν} P).pushouts) outer.F).sections :=
  ChosenStages.chosenSection (MorphismProperty.transfiniteCompositions.{w'}
    (MorphismProperty.coproducts.{ν} P).pushouts) outer.F k R
    (representative_mem P k K c)

/-- The actual same-original-order auxiliary target diagram. -/
def originalTarget : J ⥤ C :=
  ChosenStages.targetDiagram (MorphismProperty.transfiniteCompositions.{w'}
    (MorphismProperty.coproducts.{ν} P).pushouts) outer.F k R
    (representative_mem P k K c)

/-- Both pushouts push each supplied whole inner history forward on its original shape. -/
def pushedOriginalHistory (i : {j : J // ¬ IsMax j}) :
    (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape (K i).carrier
      ((originalTarget P outer k R K c).map (homOfLE (Order.le_succ i.1))) := by
  let Q := MorphismProperty.transfiniteCompositions.{w'}
    (MorphismProperty.coproducts.{ν} P).pushouts
  let x := originalSection P outer k R K c
  let S := x.val (Opposite.op i.1)
  let R' := PrefixSplitSuccessor.transportOriginalRetract Q outer.F i.1 S (k i) (R i)
  let next := PrefixSplitSuccessor.nextMap Q outer.F i.1 S (k i) R'
  let a := R'.r.left ≫ (S.D.obj ⟨i.1, le_rfl⟩).inclusion
  have sq := SplitObject.originalSuccessorPushout (S.D.obj ⟨i.1, le_rfl⟩)
    (PrefixSplitSuccessor.sourceMap Q outer.F i.1 S) (k i) R'
  let pushed := (c i).cobaseChange a sq
  have hA := ChosenStages.targetDiagram_arrowSucc Q outer.F k R
    (representative_mem P k K c) i.1 i.2
  let shifted := pushed.ofArrowIso (eqToIso hA.symm)
  exact shifted.ofLE
    (MorphismProperty.pushouts_le (P := (MorphismProperty.coproducts.{ν} P).pushouts))

/-- The actual original endpoint assembly of the precisely chosen whole family. -/
def originalEndpoint : EndpointOfSectionData
    (MorphismProperty.transfiniteCompositions.{w'} (MorphismProperty.coproducts.{ν} P).pushouts)
    outer (originalSection P outer k R K c) :=
  endpointOfSection _ outer (originalSection P outer k R K c)

/-- The retained linear order on each completed original inner history. -/
noncomputable local instance completedLinear (j : J) :
    LinearOrder (originalCompletedFamily K j) := (completeOriginalShapes K j).linearOrder
/-- The original bottom of each completed inner history. -/
noncomputable local instance completedBot (j : J) :
    OrderBot (originalCompletedFamily K j) := (completeOriginalShapes K j).orderBot
/-- The retained successor structure on each completed original inner history. -/
noncomputable local instance completedSucc (j : J) :
    SuccOrder (originalCompletedFamily K j) := (completeOriginalShapes K j).succOrder
local instance completedWF (j : J) : WellFoundedLT (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).wellFounded
local instance : WellFoundedLT (Index (originalCompletedFamily K)) := lexWellFounded
/-- The actual successor structure on the dependent lexicographic order of all inner histories. -/
noncomputable local instance : SuccOrder (Index (originalCompletedFamily K)) := flatSuccOrder

/-- The actual supplied inner histories normalize at the unchanged auxiliary endpoint arrow. -/
def normalizedOriginalTarget
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
      (Index (originalCompletedFamily K)) (originalEndpoint P outer k R K c).arrow :=
  normalizeOriginalCellular
    (originalEndpoint P outer k R K c).presentation.toTransfiniteCompositionOfShape
    K (fun i => (pushedOriginalHistory P outer k R K c i).toTransfiniteCompositionOfShape) P
    (fun i j hj => (pushedOriginalHistory P outer k R K c i).map_mem j hj)
    emptySource emptyTarget hSource hTarget

include R c in
/-- Actual original cellular representatives produce the full same-source natural splitting and a
single cellular presentation, preserving every original nonmaximal inner shape. -/
theorem existsOriginalTransfiniteCellularAbsorption
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    ∃ (Z : C) (g : X ⟶ Z)
      (_flat : (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
        (Index (originalCompletedFamily K)) g)
      (G : J ⥤ C) (d : CategoryTheory.TransfiniteCompositionOfShape J g)
      (_inner : ∀ i : {j : J // ¬ IsMax j},
        (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape (K i).carrier
          (G.map (homOfLE (Order.le_succ i.1))))
      (incl : outer.F ⟶ G) (ret : G ⟶ outer.F) (h : RetractArrow f g),
      d.F = G ∧ incl ≫ ret = 𝟙 outer.F ∧ h.i.left = 𝟙 X ∧ h.r.left = 𝟙 X := by
  let x := originalSection P outer k R K c
  let E := originalEndpoint P outer k R K c
  let G := originalTarget P outer k R K c
  exact ⟨E.target, E.arrow, normalizedOriginalTarget P outer k R K c
      emptySource emptyTarget hSource hTarget,
    G, E.presentation.toTransfiniteCompositionOfShape,
    pushedOriginalHistory P outer k R K c,
    inclusionOfSection _ outer x, retractionOfSection _ outer x, E.retract,
    E.targetDiagram_eq, section_natural_splitting _ outer x,
    E.inclusion_source, E.retraction_source⟩

include R c in
/-- The original arrow belongs to retracts of cellular presentations
in the combined order universe. -/
theorem mem_cellular_retracts
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    (MorphismProperty.transfiniteCompositions.{max w w'}
      (MorphismProperty.coproducts.{ν} P).pushouts).retracts f := by
  obtain ⟨Z, g, flat, _G, _d, _inner, _incl, _ret, h, _hD, _hSplit, _hI, _hR⟩ :=
    existsOriginalTransfiniteCellularAbsorption P outer k R K c
      emptySource emptyTarget hSource hTarget
  have hg := MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions
    (MorphismProperty.coproducts.{ν} P).pushouts (Index (originalCompletedFamily K)) g flat.mem
  exact ⟨X, Z, g, h, hg⟩

end CategoryTheory.SmallObject.CoherentRetracts.ChosenCellularStages

namespace CategoryTheory.SmallObject.CoherentRetracts

open CellularNormalization
universe ν
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (P : MorphismProperty C) {X Y : C} {f : X ⟶ Y}

/-- Actual transfinite chains of retracts of cellular arrows are retracts of a constructed
single cellular arrow. Original source and ordered chain data are the input. -/
theorem cellular_retracts_of_transfiniteComposition
    (outer : (MorphismProperty.transfiniteCompositions.{w}
      (MorphismProperty.coproducts.{ν} P).pushouts).retracts.TransfiniteCompositionOfShape J f)
    (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
    (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget) :
    (MorphismProperty.transfiniteCompositions.{w}
      (MorphismProperty.coproducts.{ν} P).pushouts).retracts f := by
  classical
  have hStages := fun i : {j : J // ¬ IsMax j} => outer.map_mem i.1 i.2
  choose A B k R hk using hStages
  have hHistories : ∀ i : {j : J // ¬ IsMax j},
      ∃ S : OriginalInnerShape.{w},
        Nonempty ((MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
          S.carrier (k i)) := by
    intro i
    obtain ⟨K, hlin, hsucc, hbot, hwf, hc⟩ :=
      (MorphismProperty.transfiniteCompositions_iff _ (k i)).1 (hk i)
    let S : OriginalInnerShape.{w} :=
      { carrier := K, linearOrder := hlin, orderBot := hbot,
        succOrder := hsucc, wellFounded := hwf }
    exact ⟨S, hc⟩
  choose K hc using hHistories
  let c := fun i => Classical.choice (hc i)
  exact ChosenCellularStages.mem_cellular_retracts P outer.toTransfiniteCompositionOfShape k R K c
    emptySource emptyTarget hSource hTarget

end CategoryTheory.SmallObject.CoherentRetracts
