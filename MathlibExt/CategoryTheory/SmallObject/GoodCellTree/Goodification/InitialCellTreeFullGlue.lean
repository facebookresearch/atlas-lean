/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreePredecessorGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyStageEquality
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Full original gluing with an actual tree and its proved preservation

The checked construction returns the same actual selected-stage tree and
its derived full preservation equations. The pair uses the standard
subtype, retaining the original tree and all maps without generating
a separate dependent equality eliminator for another tree structure.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.InitialCellTreeFullGlue

open Limits LowerSetColimits InitialFunctorFamilyGlue
  InitialFunctorFamilyStageEquality InitialCellTreeFullCompatibility

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

/-- Full preservation concerns the actual original stage fields and whole original diagram. -/
def Preserves (Q : CellTree s X (P := P)) : Prop :=
  Q.diagram = InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap ∧
  (∀ (i : I) (p : P) (hp : p ∈ S i), Q.label p = (T i).label ⟨p, hp⟩) ∧
  (∀ (i : I) (p : P) (hp : p ∈ S i),
    Q.predecessorObj p = (T i).predecessorObj ⟨p, hp⟩) ∧
  (∀ (i : I) (p : P) (hp : p ∈ S i) (q : LowerSet.Iio p),
    (Q.predecessor p).cocone.ι.app q ≍
      ((T i).predecessor ⟨p, hp⟩).cocone.ι.app
        ⟨⟨q.1, (S i).lower' q.2.le hp⟩, q.2⟩) ∧
  (∀ (i : I) (p : P) (hp : p ∈ S i), Q.attaching p ≍ (T i).attaching ⟨p, hp⟩) ∧
  (∀ (i : I) (p : P) (hp : p ∈ S i), Q.cell p ≍ (T i).cell ⟨p, hp⟩)

/-- The actual full tree is paired with its proved original preservation equations. -/
def Data := { Q : CellTree s X (P := P) // Preserves S T hCover hObj hMap Q }

/-- The same actual tree is the first component of the proved construction. -/
abbrev Data.tree (d : Data S T hCover hObj hMap) : CellTree s X (P := P) := d.1

/-- The whole actual vertex/map diagram is the original glued diagram. -/
theorem Data.diagram_eq (d : Data S T hCover hObj hMap) :
    d.tree.diagram = InitialCellTreePredecessorGlue.diagram S T hCover hObj hMap := d.2.1

/-- Every actual original stage label is retained. -/
theorem Data.labels (d : Data S T hCover hObj hMap) :
    ∀ (i : I) (p : P) (hp : p ∈ S i), d.tree.label p = (T i).label ⟨p, hp⟩ := d.2.2.1

/-- Every actual selected stage predecessor point is retained. -/
theorem Data.predecessorPoints (d : Data S T hCover hObj hMap) :
    ∀ (i : I) (p : P) (hp : p ∈ S i),
      d.tree.predecessorObj p = (T i).predecessorObj ⟨p, hp⟩ := d.2.2.2.1

/-- Every actual original predecessor cofan leg is retained on its original strict label. -/
theorem Data.predecessorLegs (d : Data S T hCover hObj hMap) :
    ∀ (i : I) (p : P) (hp : p ∈ S i) (q : LowerSet.Iio p),
      (d.tree.predecessor p).cocone.ι.app q ≍
        ((T i).predecessor ⟨p, hp⟩).cocone.ι.app
          ⟨⟨q.1, (S i).lower' q.2.le hp⟩, q.2⟩ := d.2.2.2.2.1

/-- Every actual original attaching map is retained with its dependent original types. -/
theorem Data.attaching (d : Data S T hCover hObj hMap) :
    ∀ (i : I) (p : P) (hp : p ∈ S i), d.tree.attaching p ≍ (T i).attaching ⟨p, hp⟩ :=
  d.2.2.2.2.2.1

/-- Every actual original cell map is retained with its dependent original types. -/
theorem Data.cells (d : Data S T hCover hObj hMap) :
    ∀ (i : I) (p : P) (hp : p ∈ S i), d.tree.cell p ≍ (T i).cell ⟨p, hp⟩ :=
  d.2.2.2.2.2.2

variable [HasColimitsOfSize.{w, w} C]

/-- Honest overlap equations construct the actual same tree with all original stage preservation. -/
def data (hFull : Overlap S T) : Data S T hCover hObj hMap :=
  ⟨InitialCellTreeGlue.rawTree S T hCover hObj hMap,
    ⟨rfl, label_stage S T hCover hFull,
      predecessor_point_stage S T hCover hObj hMap hFull,
      predecessor_leg_stage S T hCover hObj hMap hFull,
      attaching_stage S T hCover hObj hMap hFull, cell_stage S T hCover hObj hMap hFull⟩⟩

/-- The checked whole tree requires the actual complete stage overlap data. -/
abbrev tree (hFull : Overlap S T) : CellTree s X (P := P) :=
  (data S T hCover hObj hMap hFull).tree

/-- The paired construction retains the same actual existing selected-stage tree function. -/
theorem tree_eq (hFull : Overlap S T) :
    tree S T hCover hObj hMap hFull = InitialCellTreeGlue.rawTree S T hCover hObj hMap := rfl

/-- Each entire actual original stage diagram is preserved. -/
theorem stage_diagram (hFull : Overlap S T) (i : I) :
    restriction (tree S T hCover hObj hMap hFull).diagram (S i) = (T i).diagram :=
  InitialCellTreeGlue.rawTree_stage_diagram S T hCover hObj hMap i

/-- Every actual original stage label, predecessor point and attaching/cell map is preserved. -/
theorem stage_data (hFull : Overlap S T) (i : I) (p : P) (hp : p ∈ S i) :
    (tree S T hCover hObj hMap hFull).label p = (T i).label ⟨p, hp⟩ ∧
    (tree S T hCover hObj hMap hFull).predecessorObj p = (T i).predecessorObj ⟨p, hp⟩ ∧
    (tree S T hCover hObj hMap hFull).attaching p ≍ (T i).attaching ⟨p, hp⟩ ∧
    (tree S T hCover hObj hMap hFull).cell p ≍ (T i).cell ⟨p, hp⟩ :=
  tree_stage_data S T hCover hObj hMap hFull i p hp

/-- Actual local original goodness gives every whole original predecessor bound. -/
theorem tree_good (hFull : Overlap S T) (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hGood : ∀ i : I, (T i).IsGood chi) : (tree S T hCover hObj hMap hFull).IsGood chi :=
  InitialCellTreeGlue.rawTree_good S T hCover hObj hMap chi hGood

end CategoryTheory.SmallObject.InitialCellTreeFullGlue

namespace CategoryTheory.SmallObject.InitialCellTreeGlue

open Limits LowerSetColimits InitialCellTreeFullCompatibility

variable {P I : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  [HasColimitsOfSize.{w, w} C] {A : Type t} {s : A → Arrow C} {X : C}
  (S : I → LowerSet P) (T : ∀ i : I, CellTree s X (P := S i))
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).vertex ⟨p, hi⟩ = (T j).vertex ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (T i).diagram.map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (T j).diagram.map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))


/-- Full original gluing requires the actual stage label, predecessor and cell-data agreement. -/
abbrev tree (hFull : Overlap S T) : CellTree s X (P := P) :=
  InitialCellTreeFullGlue.tree S T hCover hObj hMap hFull

/-- The entire actual original stage diagram is retained by full original gluing. -/
theorem tree_stage_diagram (hFull : Overlap S T) (i : I) :
    restriction (tree S T hCover hObj hMap hFull).diagram (S i) = (T i).diagram :=
  InitialCellTreeFullGlue.stage_diagram S T hCover hObj hMap hFull i

/-- Full original gluing retains every actual original label, predecessor and attaching/cell map. -/
theorem tree_stage_data (hFull : Overlap S T) (i : I) (p : P) (hp : p ∈ S i) :
    (tree S T hCover hObj hMap hFull).label p = (T i).label ⟨p, hp⟩ ∧
    (tree S T hCover hObj hMap hFull).predecessorObj p = (T i).predecessorObj ⟨p, hp⟩ ∧
    (tree S T hCover hObj hMap hFull).attaching p ≍ (T i).attaching ⟨p, hp⟩ ∧
    (tree S T hCover hObj hMap hFull).cell p ≍ (T i).cell ⟨p, hp⟩ :=
  InitialCellTreeFullGlue.stage_data S T hCover hObj hMap hFull i p hp

/-- Every actual original strict predecessor label retains its complete original cofan leg. -/
theorem tree_stage_predecessor_leg (hFull : Overlap S T)
    (i : I) (p : P) (hp : p ∈ S i) (q : LowerSet.Iio p) :
    ((tree S T hCover hObj hMap hFull).predecessor p).cocone.ι.app q ≍
      ((T i).predecessor ⟨p, hp⟩).cocone.ι.app
        ⟨⟨q.1, (S i).lower' q.2.le hp⟩, q.2⟩ :=
  InitialCellTreeFullCompatibility.predecessor_leg_stage S T hCover hObj hMap hFull i p hp q

/-- Genuine local original goodness gives the complete whole good-tree bounds. -/
theorem tree_good (hFull : Overlap S T) (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hGood : ∀ i : I, (T i).IsGood chi) :
    (tree S T hCover hObj hMap hFull).IsGood chi :=
  InitialCellTreeFullGlue.tree_good S T hCover hObj hMap hFull chi hGood

end CategoryTheory.SmallObject.InitialCellTreeGlue
