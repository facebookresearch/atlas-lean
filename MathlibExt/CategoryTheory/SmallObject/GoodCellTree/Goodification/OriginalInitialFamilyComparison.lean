/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningLabelFunctors
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningStageComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalInitialFamilyCellTree
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorComparisonGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Actual whole original vertex comparisons across refining initial stages

The whole original refining cell tree has its genuine natural
transformation to the same original vertex diagram. Every component is
the actual original stage component after the derived original object
comparison. Directedness supplies full overlap compatibility from the
actual ordered stage comparisons.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalInitialFamilyComparison

open Limits LowerSetColimits InitialOrderFamilyGlue OriginalRefiningLabelFunctors

variable {P I : Type w} [pOrder : PartialOrder P] [Preorder I]
  (S : I → LowerSet P) (orders : ∀ i : I, PartialOrder (S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hMono : Monotone S)
  (hRestrict : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i),
    @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩ ↔
      @LE.le (S j) (orders j).toLE ⟨a, hMono hij ha⟩ ⟨b, hMono hij hb⟩)
  (hInitial : ∀ (i j : I) (_ : i ≤ j) (a b : S j), b.1 ∈ S i →
    @LE.le (S j) (orders j).toLE a b → a.1 ∈ S i)
  (hBelow : ∀ (i : I) (a b : S i),
    @LE.le (S i) (orders i).toLE a b → a.1 ≤ b.1)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : ∀ i : I, letI := orders i; CellTree s X (P := S i))
  (hObjects : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (letI := orders i; (T i).vertex ⟨p, hi⟩) =
      (letI := orders j; (T j).vertex ⟨p, hj⟩))
  (hMaps : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i)
    (hab : @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩),
    (letI := orders i
     letI : Preorder (S i) := (orders i).toPreorder
     (T i).diagram.map (homOfLE hab : (⟨a, ha⟩ : S i) ⟶ ⟨b, hb⟩)) ≍
      (letI := orders j
       letI : Preorder (S j) := (orders j).toPreorder
       (T j).diagram.map
         (homOfLE ((hRestrict i j hij a b ha hb).1 hab) :
           (⟨a, hMono hij ha⟩ : S j) ⟶ ⟨b, hMono hij hb⟩)))
  (Y : P ⥤ Under X)
  (beta : ∀ i : I,
    letI := orders i
    letI : Preorder (S i) := (orders i).toPreorder
    (T i).diagram ⟶ localOriginalDiagram S orders hBelow Y i)
  (hBetas : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (letI := orders i
     letI : Preorder (S i) := (orders i).toPreorder
     (beta i).app ⟨p, hi⟩) ≍
    (letI := orders j
     letI : Preorder (S j) := (orders j).toPreorder
     (beta j).app ⟨p, hj⟩))

/-- The actual whole original natural comparison is constructed from real original stage maps. -/
def rawComparison :
    let Q := OriginalInitialFamilyCellTree.rawTree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T hObjects hMaps
    let Z := wholeOriginalDiagram S orders hDirected hMono hRestrict hBelow hCover Y
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    Q.diagram ⟶ Z := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let b := OriginalRefiningStageComparison.comparison S orders hDirected hMono hRestrict
    hInitial hBelow hCover T Y beta
  let hb := OriginalRefiningStageComparison.components_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T Y beta hBetas
  let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
  letI := order S orders hDirected hMono hRestrict hBelow hCover
  exact @InitialFunctorComparisonGlue.comparison P I P
    (order (pOrder := pOrder) S orders hDirected hMono hRestrict hBelow hCover)
    pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
    L (fun i => (G i).diagram) hCover ho hm f Y b hb

/-- Every whole original component is the same actual component of any containing original stage. -/
theorem rawComparison_component (i : I) (p : P) (hp : p ∈ S i) :
    let b := rawComparison S orders hDirected hMono hRestrict hInitial hBelow hCover
      T hObjects hMaps Y beta hBetas
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    b.app p ≍
      (letI := orders i
       letI : Preorder (S i) := (orders i).toPreorder
       (beta i).app ⟨p, hp⟩) := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let b := OriginalRefiningStageComparison.comparison S orders hDirected hMono hRestrict
    hInitial hBelow hCover T Y beta
  let hb := OriginalRefiningStageComparison.components_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T Y beta hBetas
  let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact @InitialFunctorComparisonGlue.component_heq P I P
    (order (pOrder := pOrder) S orders hDirected hMono hRestrict hBelow hCover)
    pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
    L (fun i => (G i).diagram) hCover ho f Y b hb i p hp

end CategoryTheory.SmallObject.OriginalInitialFamilyComparison

namespace CategoryTheory.SmallObject.OriginalInitialFamilyComparison

open Limits LowerSetColimits InitialOrderFamilyGlue OriginalRefiningLabelFunctors

variable {P I : Type w} [pOrder : PartialOrder P] [Preorder I]
  (S : I → LowerSet P) (orders : ∀ i : I, PartialOrder (S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hMono : Monotone S)
  (hRestrict : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i),
    @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩ ↔
      @LE.le (S j) (orders j).toLE ⟨a, hMono hij ha⟩ ⟨b, hMono hij hb⟩)
  (hInitial : ∀ (i j : I) (_ : i ≤ j) (a b : S j), b.1 ∈ S i →
    @LE.le (S j) (orders j).toLE a b → a.1 ∈ S i)
  (hBelow : ∀ (i : I) (a b : S i),
    @LE.le (S i) (orders i).toLE a b → a.1 ≤ b.1)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : ∀ i : I, letI := orders i; CellTree s X (P := S i))
  (hObjects : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (letI := orders i; (T i).vertex ⟨p, hi⟩) =
      (letI := orders j; (T j).vertex ⟨p, hj⟩))
  (hMaps : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i)
    (hab : @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩),
    (letI := orders i
     letI : Preorder (S i) := (orders i).toPreorder
     (T i).diagram.map (homOfLE hab : (⟨a, ha⟩ : S i) ⟶ ⟨b, hb⟩)) ≍
      (letI := orders j
       letI : Preorder (S j) := (orders j).toPreorder
       (T j).diagram.map
         (homOfLE ((hRestrict i j hij a b ha hb).1 hab) :
           (⟨a, hMono hij ha⟩ : S j) ⟶ ⟨b, hMono hij hb⟩)))
  (hFull :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    InitialCellTreeFullCompatibility.Overlap L G)
  (Y : P ⥤ Under X)
  (beta : ∀ i : I,
    letI := orders i
    letI : Preorder (S i) := (orders i).toPreorder
    (T i).diagram ⟶ localOriginalDiagram S orders hBelow Y i)
  (hBetas : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (letI := orders i
     letI : Preorder (S i) := (orders i).toPreorder
     (beta i).app ⟨p, hi⟩) ≍
    (letI := orders j
     letI : Preorder (S j) := (orders j).toPreorder
     (beta j).app ⟨p, hj⟩))

/-- The actual whole original natural comparison is constructed from real original stage maps. -/
def comparison :
    let Q := OriginalInitialFamilyCellTree.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T hObjects hMaps hFull
    let Z := wholeOriginalDiagram S orders hDirected hMono hRestrict hBelow hCover Y
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    Q.diagram ⟶ Z := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let b := OriginalRefiningStageComparison.comparison S orders hDirected hMono hRestrict
    hInitial hBelow hCover T Y beta
  let hb := OriginalRefiningStageComparison.components_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T Y beta hBetas
  let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
  letI := order S orders hDirected hMono hRestrict hBelow hCover
  exact @InitialFunctorComparisonGlue.comparison P I P
    (order (pOrder := pOrder) S orders hDirected hMono hRestrict hBelow hCover)
    pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
    L (fun i => (G i).diagram) hCover ho hm f Y b hb

/-- Every whole original component is the same actual component of any containing original stage. -/
theorem comparison_component (i : I) (p : P) (hp : p ∈ S i) :
    let b := comparison S orders hDirected hMono hRestrict hInitial hBelow hCover
      T hObjects hMaps hFull Y beta hBetas
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    b.app p ≍
      (letI := orders i
       letI : Preorder (S i) := (orders i).toPreorder
       (beta i).app ⟨p, hp⟩) := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let b := OriginalRefiningStageComparison.comparison S orders hDirected hMono hRestrict
    hInitial hBelow hCover T Y beta
  let hb := OriginalRefiningStageComparison.components_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T Y beta hBetas
  let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact @InitialFunctorComparisonGlue.component_heq P I P
    (order (pOrder := pOrder) S orders hDirected hMono hRestrict hBelow hCover)
    pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
    L (fun i => (G i).diagram) hCover ho f Y b hb i p hp

/-- The whole checked comparison retains the same actual original map and component choices. -/
theorem comparison_eq :
    comparison S orders hDirected hMono hRestrict hInitial hBelow hCover
      T hObjects hMaps hFull Y beta hBetas =
        OriginalInitialFamilyComparison.rawComparison S orders hDirected hMono hRestrict
          hInitial hBelow hCover T hObjects hMaps Y beta hBetas := rfl

end CategoryTheory.SmallObject.OriginalInitialFamilyComparison
