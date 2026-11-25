/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreePredecessorGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyStageEquality
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# Full actual cell-data compatibility of original initial stages

The vertex diagram alone does not determine actual generator labels,
predecessor cofans, attaching maps or cell maps. Honest overlap
compatibility of those actual stage fields gives preservation of every
original stage through the same selected-stage gluing construction.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.InitialCellTreeFullCompatibility

open Limits LowerSetColimits InitialFunctorFamilyGlue InitialCellTreePredecessorGlue
  InitialFunctorFamilyStageEquality

variable {P I : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (S : I → LowerSet P) (T : ∀ i : I, CellTree s X (P := S i))

/-- Actual overlap compatibility of all original label/predecessor/attaching/cell fields. -/
structure Overlap : Prop where
  /-- Actual original generator labels agree on every whole original overlap. -/
  labels : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).label ⟨p, hi⟩ = (T j).label ⟨p, hj⟩
  /-- Actual selected original predecessor points agree, beyond vertex-diagram equality. -/
  predecessorPoints : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).predecessorObj ⟨p, hi⟩ = (T j).predecessorObj ⟨p, hj⟩
  /-- Actual original predecessor cofan legs agree on the same original strict labels. -/
  predecessorLegs : ∀ (i j : I) (p q : P) (hi : p ∈ S i) (hj : p ∈ S j) (hqp : q < p),
    ((T i).predecessor ⟨p, hi⟩).cocone.ι.app
      ⟨⟨q, (S i).lower' hqp.le hi⟩, hqp⟩ ≍
    ((T j).predecessor ⟨p, hj⟩).cocone.ι.app
      ⟨⟨q, (S j).lower' hqp.le hj⟩, hqp⟩
  /-- Actual original attaching morphisms agree with their dependent original types. -/
  attaching : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).attaching ⟨p, hi⟩ ≍ (T j).attaching ⟨p, hj⟩
  /-- Actual original cell morphisms agree with their dependent original types. -/
  cells : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).cell ⟨p, hi⟩ ≍ (T j).cell ⟨p, hj⟩

variable (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).vertex ⟨p, hi⟩ = (T j).vertex ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (T i).diagram.map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (T j).diagram.map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))
  (hFull : Overlap S T)

include hFull in
/-- Every actual whole generator occurrence retains each original stage label. -/
theorem label_stage (i : I) (p : P) (hp : p ∈ S i) :
    InitialCellTreeGlue.label S T hCover p = (T i).label ⟨p, hp⟩ :=
  hFull.labels (stage S hCover p) i p (in_stage S hCover p) hp

include hFull in
/-- Every actual whole predecessor point retains each original selected stage point. -/
theorem predecessor_point_stage (i : I) (p : P) (hp : p ∈ S i) :
    (InitialCellTreeGlue.predecessor S T hCover hObj hMap p).cocone.pt =
      (T i).predecessorObj ⟨p, hp⟩ :=
  hFull.predecessorPoints (stage S hCover p) i p (in_stage S hCover p) hp

include hFull in
/-- Every actual whole attaching morphism retains the original stage attaching function. -/
theorem attaching_stage (i : I) (p : P) (hp : p ∈ S i) :
    InitialCellTreeGlue.attaching S T hCover hObj hMap p ≍ (T i).attaching ⟨p, hp⟩ :=
  hFull.attaching (stage S hCover p) i p (in_stage S hCover p) hp

include hFull in
/-- Every actual whole cell morphism retains the original stage cell function. -/
theorem cell_stage (i : I) (p : P) (hp : p ∈ S i) :
    InitialCellTreeGlue.cell S T hCover hObj hMap p ≍ (T i).cell ⟨p, hp⟩ := by
  let k := stage S hCover p
  have hk : p ∈ S k := in_stage S hCover p
  let hVertex := (obj_eq S (fun j => (T j).diagram) hCover hObj k p hk).symm
  change (T k).cell ⟨p, hk⟩ ≫ (eqToHom hVertex).right ≍ (T i).cell ⟨p, hp⟩
  rw [Under.eqToHom_right]
  exact (comp_eqToHom_heq ((T k).cell ⟨p, hk⟩) (congrArg Under.right hVertex)).trans
    (hFull.cells k i p hk hp)

include hFull in
/-- Every actual whole predecessor leg retains the original stage cofan on its literal label. -/
theorem predecessor_leg_stage (i : I) (p : P) (hp : p ∈ S i) (q : LowerSet.Iio p) :
    (InitialCellTreeGlue.predecessor S T hCover hObj hMap p).cocone.ι.app q ≍
      ((T i).predecessor ⟨p, hp⟩).cocone.ι.app
        ⟨⟨q.1, (S i).lower' q.2.le hp⟩, q.2⟩ := by
  let k := stage S hCover p
  have hk : p ∈ S k := in_stage S hCover p
  have hl := InitialCellTreePredecessorGlue.predecessor_leg S T hCover hObj hMap k p hk q
  change (InitialCellTreePredecessorGlue.predecessor S T hCover hObj hMap k p hk).cocone.ι.app q ≍ _
  apply (heq_of_eq hl).trans
  exact (eqToHom_comp_heq
    (((T k).predecessor ⟨p, hk⟩).cocone.ι.app ((predecessorOrderIso S k p hk).symm q))
    (obj_eq S (fun j => (T j).diagram) hCover hObj k q.1 ((S k).lower' q.2.le hk))).trans
      (hFull.predecessorLegs k i p q.1 hk hp q.2)

variable [HasColimitsOfSize.{w, w} C]

include hFull in
/-- All original stage label, selected predecessor, attaching and cell data are preserved. -/
theorem tree_stage_data (i : I) (p : P) (hp : p ∈ S i) :
    (InitialCellTreeGlue.rawTree S T hCover hObj hMap).label p = (T i).label ⟨p, hp⟩ ∧
    (InitialCellTreeGlue.rawTree S T hCover hObj hMap).predecessorObj p =
      (T i).predecessorObj ⟨p, hp⟩ ∧
    (InitialCellTreeGlue.rawTree S T hCover hObj hMap).attaching p ≍ (T i).attaching ⟨p, hp⟩ ∧
    (InitialCellTreeGlue.rawTree S T hCover hObj hMap).cell p ≍ (T i).cell ⟨p, hp⟩ := by
  exact ⟨label_stage S T hCover hFull i p hp,
    predecessor_point_stage S T hCover hObj hMap hFull i p hp,
    attaching_stage S T hCover hObj hMap hFull i p hp,
    cell_stage S T hCover hObj hMap hFull i p hp⟩

end CategoryTheory.SmallObject.InitialCellTreeFullCompatibility
