/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyStageEquality
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreePredecessorGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Genuine whole cell trees glued from compatible actual initial stages

Actual stage vertices and maps construct the whole diagram. Every strict
predecessor cocone is the transported actual stage cocone; every cell
square is its original stage pushout after the actual vertex comparison.
The endpoint is an actual coefficient colimit. Local goodness gives every
whole predecessor bound without bounding the whole cell carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.InitialCellTreeGlue

open Limits LowerSetColimits InitialFunctorFamilyGlue
  InitialFunctorFamilyStageEquality InitialCellTreePredecessorGlue

variable {P I : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (S : I → LowerSet P) (T : ∀ i : I, CellTree s X (P := S i))
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).vertex ⟨p, hi⟩ = (T j).vertex ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (T i).diagram.map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (T j).diagram.map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))

include T hCover in
/-- Actual initial-stage well-foundedness proves the whole original refining order well founded. -/
theorem wellFounded : WellFounded ((· < ·) : P → P → Prop) := by
  constructor
  intro p
  let i := stage S hCover p
  have hp : p ∈ S i := in_stage S hCover p
  have hAcc : ∀ a : S i, Acc ((· < ·) : P → P → Prop) a.1 := by
    intro a
    induction (T i).wellFounded.apply a with
    | intro a _ ih =>
      refine Acc.intro a.1 ?_
      intro q hq
      exact ih ⟨q, (S i).lower' hq.le a.2⟩ hq
  exact hAcc ⟨p, hp⟩

/-- Each original label keeps the actual original generator of its selected real stage. -/
def label (p : P) : A :=
  (T (stage S hCover p)).label ⟨p, in_stage S hCover p⟩

/-- The actual whole predecessor data is the already proved selected stage predecessor colimit. -/
abbrev predecessor (p : P) :
    ColimitCocone (restriction
      (InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap) (LowerSet.Iio p)) :=
  InitialCellTreePredecessorGlue.predecessor S T hCover hObj hMap
    (stage S hCover p) p (in_stage S hCover p)

/-- Every whole attaching map is the same actual attaching map of the selected original stage. -/
def attaching (p : P) :
    (s (label S T hCover p)).left ⟶ (predecessor S T hCover hObj hMap p).cocone.pt.right :=
  (T (stage S hCover p)).attaching ⟨p, in_stage S hCover p⟩

/-- Every whole cell map is its actual original stage cell with the actual vertex comparison. -/
def cell (p : P) :
    (s (label S T hCover p)).right ⟶
      ((InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap).obj p).right :=
  (T (stage S hCover p)).cell ⟨p, in_stage S hCover p⟩ ≫
    (eqToHom (obj_eq S (fun i => (T i).diagram) hCover hObj
      (stage S hCover p) p (in_stage S hCover p)).symm).right

/-- Every whole original cell square is constructed from its real selected stage pushout. -/
theorem isPushout (p : P) :
    IsPushout (attaching S T hCover hObj hMap p) (s (label S T hCover p)).hom
      (cellTreePredecessorMap
        (InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap) p
        (predecessor S T hCover hObj hMap p)).right (cell S T hCover hObj hMap p) := by
  let i := stage S hCover p
  have hp : p ∈ S i := in_stage S hCover p
  let e : (T i).vertex ⟨p, hp⟩ ≅
      (InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap).obj p :=
    eqToIso (obj_eq S (fun i => (T i).diagram) hCover hObj i p hp).symm
  apply ((T i).isPushout ⟨p, hp⟩).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ((Under.forget X).mapIso e)
  · change (T i).attaching ⟨p, hp⟩ ≫ 𝟙 _ = 𝟙 _ ≫ (T i).attaching ⟨p, hp⟩
    simp only [Category.comp_id, Category.id_comp]
  · change (s ((T i).label ⟨p, hp⟩)).hom ≫ 𝟙 _ =
      𝟙 _ ≫ (s ((T i).label ⟨p, hp⟩)).hom
    simp only [Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, Under.forget_map]
    change ((T i).predecessorMap ⟨p, hp⟩).right ≫ e.hom.right = _
    have hm := predecessorMap_eq S T hCover hObj hMap i p hp
    exact (congrArg Under.Hom.right hm).symm
  · change (T i).cell ⟨p, hp⟩ ≫ e.hom.right =
      𝟙 _ ≫ ((T i).cell ⟨p, hp⟩ ≫ e.hom.right)
    rw [Category.id_comp]

variable [HasColimitsOfSize.{w, w} C]

/-- The whole tree has constructed predecessor, cell and endpoint universal properties. -/
def rawTree : CellTree s X (P := P) where
  wellFounded := wellFounded S T hCover
  diagram := InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap
  label := label S T hCover
  predecessor := predecessor S T hCover hObj hMap
  attaching := attaching S T hCover hObj hMap
  cell := cell S T hCover hObj hMap
  isPushout := isPushout S T hCover hObj hMap
  endpoint :=
    ⟨colimit.cocone (InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap),
      colimit.isColimit (InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap)⟩

/-- The whole vertex functor restricts to every actual original stage as an entire functor. -/
theorem rawTree_stage_diagram (i : I) :
    restriction (rawTree S T hCover hObj hMap).diagram (S i) = (T i).diagram :=
  stage_eq S (fun i => (T i).diagram) hCover hObj hMap i

/-- Actual local goodness proves all whole predecessor bounds on the same whole original carrier. -/
theorem rawTree_good (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hGood : ∀ i : I, (T i).IsGood chi) : (rawTree S T hCover hObj hMap).IsGood chi where
  presentable_source p := (hGood (stage S hCover p)).presentable_source
    ⟨p, in_stage S hCover p⟩
  presentable_target p := (hGood (stage S hCover p)).presentable_target
    ⟨p, in_stage S hCover p⟩
  predecessor_lt p :=
    ((hGood (stage S hCover p)).predecessor_lt ⟨p, in_stage S hCover p⟩).of_injective
      (predecessorOrderIso S (stage S hCover p) p (in_stage S hCover p)).symm
      (predecessorOrderIso S (stage S hCover p) p (in_stage S hCover p)).symm.injective

end CategoryTheory.SmallObject.InitialCellTreeGlue
