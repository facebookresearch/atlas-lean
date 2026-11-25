/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalInitialFamilyCellTree
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalInitialFamilyComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalInitialFamilyLowerColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerRestrictionComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningLabelFunctors
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone

/-!
# Full original overlapping-restriction gluing owner

Every stage is an actual lower restriction of the same original cell
tree with the same selected lower-colimit choices. All order, diagram,
cell-data and comparison overlap equations are derived. The owner joins
the checked tree, comparison and every original lower UP, including the
actual empty stage and the original whole stage.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace MathlibExtTest.InitialCellTreeFullGluing

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  LowerSetColimits InitialOrderFamilyGlue OriginalRefiningLabelFunctors

variable {P : Type w} [pOrder : PartialOrder P]

/-- The whole chosen index consists of every actual original lower set. -/
abbrev stages : LowerSet P → LowerSet P := id

/-- Every actual stage order is inherited from the same original order. -/
abbrev orders : ∀ B : LowerSet P, PartialOrder (stages B) := fun _ => inferInstance

/-- The same actual original union gives a common upper stage. -/
theorem directed (B D : LowerSet P) : ∃ E : LowerSet P, B ≤ E ∧ D ≤ E :=
  ⟨B ⊔ D, le_sup_left, le_sup_right⟩

/-- Actual original lower sets are monotone in their literal inclusion order. -/
theorem mono : Monotone (stages (P := P)) := monotone_id

/-- The original order on every smaller stage is its actual inherited larger-stage order. -/
theorem restrict (B D : LowerSet P) (h : B ≤ D) (p q : P) (hp : p ∈ B) (hq : q ∈ B) :
    @LE.le (stages B) (orders B).toLE ⟨p, hp⟩ ⟨q, hq⟩ ↔
      @LE.le (stages D) (orders D).toLE ⟨p, h hp⟩ ⟨q, h hq⟩ := Iff.rfl

/-- Each actual original lower subset is initial in every containing original lower stage. -/
theorem initial (B D : LowerSet P) (_ : B ≤ D) (p q : stages D) (hq : q.1 ∈ B)
    (h : @LE.le (stages D) (orders D).toLE p q) : p.1 ∈ B := B.lower' h hq

/-- Every actual inherited stage comparison is the same original comparison. -/
theorem below (B : LowerSet P) (p q : stages B)
    (h : @LE.le (stages B) (orders B).toLE p q) : p.1 ≤ q.1 := h

/-- The actual original whole lower stage covers every original label. -/
theorem cover (p : P) : ∃ B : LowerSet P, p ∈ stages B := ⟨⊤, by simp⟩

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)

/-- The actual entire original lower-stage trees keep all original choices. -/
abbrev trees : ∀ B : LowerSet P, letI := orders B; CellTree s X (P := stages B) :=
  fun B => CellTreeLowerRestriction.tree O M B

omit [HasColimitsOfSize.{w, w} C] in
/-- All actual overlapping original vertex objects agree literally. -/
theorem objects (B D : LowerSet P) (_ : B ≤ D) (p : P) (hp : p ∈ B) (hq : p ∈ D) :
    (letI := orders B; (trees O M B).vertex ⟨p, hp⟩) =
      (letI := orders D; (trees O M D).vertex ⟨p, hq⟩) := rfl

omit [HasColimitsOfSize.{w, w} C] in
/-- All actual overlapping original diagram maps agree on their literal original labels. -/
theorem maps (B D : LowerSet P) (h : B ≤ D) (p q : P) (hp : p ∈ B) (hq : q ∈ B)
    (hpq : @LE.le (stages B) (orders B).toLE ⟨p, hp⟩ ⟨q, hq⟩) :
    (letI := orders B; letI : Preorder (stages B) := (orders B).toPreorder
     (trees O M B).diagram.map (homOfLE hpq : (⟨p, hp⟩ : stages B) ⟶ ⟨q, hq⟩)) ≍
    (letI := orders D; letI : Preorder (stages D) := (orders D).toPreorder
     (trees O M D).diagram.map
       (homOfLE ((restrict B D h p q hp hq).1 hpq) :
         (⟨p, h hp⟩ : stages D) ⟶ ⟨q, h hq⟩)) := HEq.rfl

omit [HasColimitsOfSize.{w, w} C] in
/-- Full actual cell-data agreement comes from the same original tree on every overlap. -/
theorem overlap :
    let L := lower (P := P) stages orders directed mono restrict below cover
    let G := InitialOrderCellTreeReindex.tree stages orders directed mono restrict
      initial below cover (trees O M)
    letI := order (P := P) stages orders directed mono restrict below cover
    InitialCellTreeFullCompatibility.Overlap L G := by
  let : PartialOrder P := order (pOrder := pOrder) stages orders
    directed mono restrict below cover
  exact {
    labels := fun _ _ _ _ _ => rfl
    predecessorPoints := fun _ _ _ _ _ => rfl
    predecessorLegs := fun _ _ _ _ _ _ _ => HEq.rfl
    attaching := fun _ _ _ _ _ => HEq.rfl
    cells := fun _ _ _ _ _ => HEq.rfl }

/-- The actual same original carrier has its constructed whole order. -/
abbrev wholeOrder : PartialOrder P :=
  order (P := P) stages orders directed mono restrict below cover

/-- The checked whole original tree uses the actual original restriction fields. -/
def tree : letI := wholeOrder (P := P); CellTree s X (P := P) :=
  OriginalInitialFamilyCellTree.tree stages orders directed mono restrict initial below cover
    (trees O M) (objects O M) (maps O M) (overlap O M)

/-- Every containing original stage preserves every actual original cell field. -/
theorem stage_data (B : LowerSet P) (p : P) (hp : p ∈ B) :
    letI := wholeOrder (P := P)
    (tree (pOrder := pOrder) O M).label p = (letI := pOrder; O.label p) ∧
    (tree (pOrder := pOrder) O M).predecessorObj p = (letI := pOrder; O.predecessorObj p) ∧
    (tree (pOrder := pOrder) O M).attaching p ≍ (letI := pOrder; O.attaching p) ∧
    (tree (pOrder := pOrder) O M).cell p ≍ (letI := pOrder; O.cell p) :=
  OriginalInitialFamilyCellTree.tree_stage_data stages orders directed mono restrict
    initial below cover (trees O M) (objects O M) (maps O M) (overlap O M) B p hp

/-- The original complete predecessor map is retained at the original whole stage. -/
theorem predecessor_map (p : P) :
    letI := wholeOrder (P := P)
    (tree (pOrder := pOrder) O M).predecessorMap p ≍ (letI := pOrder; O.predecessorMap p) := by
  have h := OriginalInitialFamilyCellTree.tree_stage_predecessor_map stages orders
    directed mono restrict initial below cover (trees O M) (objects O M) (maps O M)
    (overlap O M) ⊤ p (by simp)
  exact h.trans (heq_of_eq (CellTreeLowerRestriction.predecessorMap O ⊤ ⟨p, by simp⟩))

/-- Every original stage comparison is its actual original identity natural map. -/
abbrev beta (B : LowerSet P) :
    letI := orders B
    letI : Preorder (stages B) := (orders B).toPreorder
    (trees O M B).diagram ⟶ localOriginalDiagram stages orders below O.diagram B :=
  OriginalLowerRestrictionComparison.comparison O M B

omit [HasColimitsOfSize.{w, w} C] in
/-- Every actual original identity comparison agrees on full original overlaps. -/
theorem betas (B D : LowerSet P) (_ : B ≤ D) (p : P) (hp : p ∈ B) (hq : p ∈ D) :
    (letI := orders B; letI : Preorder (stages B) := (orders B).toPreorder
     (beta O M B).app ⟨p, hp⟩) ≍
      (letI := orders D; letI : Preorder (stages D) := (orders D).toPreorder
       (beta O M D).app ⟨p, hq⟩) := HEq.rfl

/-- The checked whole comparison is built from the actual original identity stage maps. -/
abbrev wholeComparison :=
  OriginalInitialFamilyComparison.comparison stages orders directed mono restrict
    initial below cover (trees O M) (objects O M) (maps O M) (overlap O M)
    O.diagram (beta O M) (betas O M)

/-- Every complete whole comparison component is the original identity under-map. -/
theorem whole_component (p : P) :
    letI := wholeOrder (P := P)
    (wholeComparison (pOrder := pOrder) O M).app p ≍ 𝟙 ((letI := pOrder; O.vertex p)) :=
  OriginalInitialFamilyComparison.comparison_component stages orders directed mono restrict
    initial below cover (trees O M) (objects O M) (maps O M) (overlap O M)
    O.diagram (beta O M) (betas O M) ⊤ p (by simp)

/-- Each old stage lower UP is derived from the same complete original selected lower UP. -/
def localUP (B D : LowerSet P) (h : D ≤ B) :
    letI := orders B
    letI : Preorder (stages B) := (orders B).toPreorder
    IsColimit (OriginalLowerComparisonCocone.cocone (localLabels stages orders below B)
      (trees O M B).diagram O.diagram (beta O M B) M D) :=
  OriginalLowerRestrictionComparison.lowerIsColimit O M B D h

/-- Every original lower comparison has its actual derived whole UP under the same original root. -/
def wholeLowerColimit (D : LowerSet P) :=
  OriginalInitialFamilyLowerColimits.isColimit stages orders directed mono restrict
    initial below cover (trees O M) (objects O M) (maps O M) (overlap O M)
    O.diagram (beta O M) (betas O M) M (localUP O M) D

/-- The literal original empty lower carrier is an actual stage of the whole chosen index. -/
def emptyStage : LowerSet P where
  carrier := ∅
  lower' := fun _ _ _ h => False.elim h

/-- The actual empty original stage has no invented original generator occurrences. -/
theorem empty_stage : IsEmpty (stages (emptyStage (P := P))) :=
  ⟨fun p => p.2⟩

/-- Every actual original whole-stage occurrence retains its original cell and attaching maps. -/
theorem whole_stage (p : P) :
    letI := wholeOrder (P := P)
    (tree (pOrder := pOrder) O M).label p = (letI := pOrder; O.label p) ∧
    (tree (pOrder := pOrder) O M).predecessorObj p = (letI := pOrder; O.predecessorObj p) ∧
    (tree (pOrder := pOrder) O M).attaching p ≍ (letI := pOrder; O.attaching p) ∧
    (tree (pOrder := pOrder) O M).cell p ≍ (letI := pOrder; O.cell p) :=
  stage_data O M ⊤ p (by simp)

omit [HasColimitsOfSize.{w, w} C] in
/-- Two actual nonempty overlapping original stages retain the same original full cell data. -/
theorem overlapping_stages (B D : LowerSet P) (p : P) (hp : p ∈ B) (hq : p ∈ D) :
    (trees O M B).label ⟨p, hp⟩ = (trees O M D).label ⟨p, hq⟩ ∧
    (trees O M B).predecessorObj ⟨p, hp⟩ = (trees O M D).predecessorObj ⟨p, hq⟩ ∧
    (trees O M B).attaching ⟨p, hp⟩ ≍ (trees O M D).attaching ⟨p, hq⟩ ∧
    (trees O M B).cell ⟨p, hp⟩ ≍ (trees O M D).cell ⟨p, hq⟩ :=
  ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩

/-- The empty-boundary client uses the same actual original selected lower colimit. -/
def emptyLowerColimit := wholeLowerColimit O M (emptyStage (P := P))

end MathlibExtTest.InitialCellTreeFullGluing
