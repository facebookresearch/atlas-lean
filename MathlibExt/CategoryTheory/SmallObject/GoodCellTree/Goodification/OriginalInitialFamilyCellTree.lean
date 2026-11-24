/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullPredecessorMap
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeFullReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic


/-!
# Whole original cell-tree limits from actual compatible refining stages

The original stage orders construct the whole refining order on the same
original carrier. Their actual full vertex diagrams and original ordered
compatibility then construct the whole cell tree, including every
predecessor and endpoint colimit and cell pushout. Actual local goodness
proves the whole tree is good, without any whole carrier bound.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalInitialFamilyCellTree

open Limits LowerSetColimits InitialOrderFamilyGlue

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

/-- The whole original cell tree is constructed from actual refining initial stages. -/
def rawTree :
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    CellTree s X (P := P) := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  letI := order S orders hDirected hMono hRestrict hBelow hCover
  have hc : ∀ p : P, ∃ i : I, p ∈ L i := hCover
  exact InitialCellTreeGlue.rawTree L G hc ho hm

/-- Every actual whole original stage restriction keeps its complete original reindexed diagram. -/
theorem rawTree_stage_diagram (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    let Q := rawTree S orders hDirected hMono hRestrict hInitial hBelow hCover T hObjects hMaps
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    restriction Q.diagram (L i) = (G i).diagram := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact InitialCellTreeGlue.rawTree_stage_diagram L G hCover ho hm i

/-- Every original local support bound proves the whole constructed original tree is good. -/
theorem rawTree_good (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hGood : ∀ i : I, letI := orders i; (T i).IsGood chi) :
    let Q := rawTree S orders hDirected hMono hRestrict hInitial hBelow hCover T hObjects hMaps
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    Q.IsGood chi := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let hg := fun i : I => InitialOrderCellTreeReindex.tree_good S orders hDirected hMono
    hRestrict hInitial hBelow hCover T i chi (hGood i)
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact InitialCellTreeGlue.rawTree_good L G hCover ho hm chi hg

end CategoryTheory.SmallObject.OriginalInitialFamilyCellTree

namespace CategoryTheory.SmallObject.OriginalInitialFamilyCellTree

open Limits LowerSetColimits InitialOrderFamilyGlue

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

variable
  (hFull :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    InitialCellTreeFullCompatibility.Overlap L G)

/-- The whole original cell tree is constructed from actual refining initial stages. -/
def tree :
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    CellTree s X (P := P) := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  letI := order S orders hDirected hMono hRestrict hBelow hCover
  have hc : ∀ p : P, ∃ i : I, p ∈ L i := hCover
  exact InitialCellTreeGlue.tree L G hc ho hm hFull

/-- Every actual whole original stage restriction keeps its complete original reindexed diagram. -/
theorem tree_stage_diagram (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    let Q := tree S orders hDirected hMono hRestrict hInitial hBelow hCover T hObjects hMaps hFull
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    restriction Q.diagram (L i) = (G i).diagram := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact InitialCellTreeFullGlue.stage_diagram L G hCover ho hm hFull i

/-- Every original local support bound proves the whole constructed original tree is good. -/
theorem tree_good (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hGood : ∀ i : I, letI := orders i; (T i).IsGood chi) :
    let Q := tree S orders hDirected hMono hRestrict hInitial hBelow hCover T hObjects hMaps hFull
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    Q.IsGood chi := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let hg := fun i : I => InitialOrderCellTreeReindex.tree_good S orders hDirected hMono
    hRestrict hInitial hBelow hCover T i chi (hGood i)
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact InitialCellTreeFullGlue.tree_good L G hCover ho hm hFull chi hg

/-- The checked whole constructor preserves the same actual existing tree and all its choices. -/
theorem tree_eq :
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    tree (pOrder := pOrder) S orders hDirected hMono hRestrict
      hInitial hBelow hCover T hObjects hMaps hFull =
      OriginalInitialFamilyCellTree.rawTree (pOrder := pOrder) S orders hDirected hMono hRestrict
        hInitial hBelow hCover T hObjects hMaps := rfl

/-- The complete original generator, predecessor-point and attaching/cell data are retained. -/
theorem tree_stage_data (i : I) (p : P) (hp : p ∈ S i) :
    let Q := tree S orders hDirected hMono hRestrict hInitial hBelow hCover
      T hObjects hMaps hFull
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    Q.label p = (letI := orders i; (T i).label ⟨p, hp⟩) ∧
    Q.predecessorObj p = (letI := orders i; (T i).predecessorObj ⟨p, hp⟩) ∧
    Q.attaching p ≍ (letI := orders i; (T i).attaching ⟨p, hp⟩) ∧
    Q.cell p ≍ (letI := orders i; (T i).cell ⟨p, hp⟩) := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact InitialCellTreeFullGlue.stage_data L G hCover ho hm hFull i p hp

/-- Every complete original predecessor cofan survives on its whole original strict labels. -/
theorem tree_stage_predecessor_leg (i : I) (p : P) (hp : p ∈ S i) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    let Q := tree S orders hDirected hMono hRestrict hInitial hBelow hCover
      T hObjects hMaps hFull
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    ∀ q : LowerSet.Iio p,
      (Q.predecessor p).cocone.ι.app q ≍
        ((G i).predecessor ⟨p, hp⟩).cocone.ι.app
          ⟨⟨q.1, (L i).lower' q.2.le hp⟩, q.2⟩ := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  exact InitialCellTreeFullCompatibility.predecessor_leg_stage
    L G hCover ho hm hFull i p hp

/-- The actual original predecessor descender is preserved by the full original cofan UP. -/
theorem tree_stage_predecessor_map (i : I) (p : P) (hp : p ∈ S i) :
    let Q := tree S orders hDirected hMono hRestrict hInitial hBelow hCover
      T hObjects hMaps hFull
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    Q.predecessorMap p ≍ (letI := orders i; (T i).predecessorMap ⟨p, hp⟩) := by
  let L := lower S orders hDirected hMono hRestrict hBelow hCover
  let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let : PartialOrder P := order S orders hDirected hMono hRestrict hBelow hCover
  have h := InitialCellTreeFullPredecessorMap.predecessor_map_stage
    L G hCover ho hm hFull i p hp
  exact h.trans (heq_of_eq
    (InitialOrderCellTreeFullReindex.predecessor_map (pOrder := pOrder)
      S orders hDirected hMono hRestrict hInitial hBelow hCover T i ⟨p, hp⟩))

end CategoryTheory.SmallObject.OriginalInitialFamilyCellTree
