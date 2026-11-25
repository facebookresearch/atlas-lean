/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerStagePieces
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialComparisonFilteredLowerColimit
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OrderIsoLowerColimitTransport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalInitialFamilyCellTree
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalInitialFamilyComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningLabelFunctors
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningStageComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone

/-!
# Actual original lower-colimit invariants for same-carrier refining limits

Every original lower set is the actual union of its original stage
intersections. Actual old stage lower-colimit UPs are reindexed through
their literal label order isomorphisms, then transported and glued.
The whole selected point and all actual original vertex legs are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalInitialFamilyLowerColimits

open Limits LowerSetColimits InitialOrderFamilyGlue OriginalRefiningLabelFunctors

variable {P I : Type w} [pOrder : PartialOrder P] [iOrder : Preorder I] [Nonempty I]
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
  {C : Type u} [cCategory : Category.{v} C] [HasColimitsOfSize.{w, w} C]
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
  (L : LowerSetColimitData Y)
  (hLocal : ∀ (i : I) (D : LowerSet P), D ≤ S i →
    letI := orders i
    letI : Preorder (S i) := (orders i).toPreorder
    IsColimit
      (OriginalLowerComparisonCocone.cocone (localLabels S orders hBelow i)
        (T i).diagram Y (beta i) L D))

/-- Actual original stage lower-colimit UPs construct every whole original lower-colimit UP. -/
def rawIsColimit (B : LowerSet P) :
    let Q := OriginalInitialFamilyCellTree.rawTree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T hObjects hMaps
    let b := OriginalInitialFamilyComparison.rawComparison S orders hDirected hMono hRestrict
      hInitial hBelow hCover T hObjects hMaps Y beta hBetas
    let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    IsColimit
      (@OriginalLowerComparisonCocone.cocone P P
        (order (pOrder := pOrder) S orders hDirected hMono hRestrict hBelow hCover).toPreorder
        pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
        f Q.diagram Y b L B) := by
  let ls := lower S orders hDirected hMono hRestrict hBelow hCover
  let gs := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let bs := OriginalRefiningStageComparison.comparison S orders hDirected hMono hRestrict
    hInitial hBelow hCover T Y beta
  let hb := OriginalRefiningStageComparison.components_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T Y beta hBetas
  let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
  let ds := OriginalLowerStagePieces.pieces S hMono B
  have hUnion := OriginalLowerStagePieces.pieces_union S hMono hCover B
  let hc := fun (i : I) (p : P) (hp : p ∈ ds.obj i) => hp.2
  let hu := fun i : I =>
    @OrderIsoLowerColimitTransport.isColimit
      (lower S orders hDirected hMono hRestrict hBelow hCover i) (S i) P
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i)
      (orders i) pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
      (stageIso S orders hDirected hMono hRestrict hInitial hBelow hCover i)
      (localLabels S orders hBelow i) (letI := orders i; (T i).diagram) Y (beta i) L
      (ds.obj i) (hLocal i (ds.obj i) inf_le_right)
  let pGlobal := order S orders hDirected hMono hRestrict hBelow hCover
  let fs := fun i : I => letI := pGlobal; (gs i).diagram
  let : IsDirectedOrder I := ⟨hDirected⟩
  have hUP := @InitialComparisonFilteredLowerColimit.isColimit P I P pGlobal
    (@Preorder.smallCategory I iOrder) (inferInstance : IsFiltered I)
    pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
    ls fs hCover ho hm f Y bs hb L ds hc hu
  rw [hUnion] at hUP
  exact hUP

end CategoryTheory.SmallObject.OriginalInitialFamilyLowerColimits

namespace CategoryTheory.SmallObject.OriginalInitialFamilyLowerColimits

open Limits LowerSetColimits InitialOrderFamilyGlue OriginalRefiningLabelFunctors

variable {P I : Type w} [pOrder : PartialOrder P] [iOrder : Preorder I] [Nonempty I]
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
  {C : Type u} [cCategory : Category.{v} C] [HasColimitsOfSize.{w, w} C]
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
  (L : LowerSetColimitData Y)
  (hLocal : ∀ (i : I) (D : LowerSet P), D ≤ S i →
    letI := orders i
    letI : Preorder (S i) := (orders i).toPreorder
    IsColimit
      (OriginalLowerComparisonCocone.cocone (localLabels S orders hBelow i)
        (T i).diagram Y (beta i) L D))

/-- Actual original stage lower-colimit UPs construct every whole original lower-colimit UP. -/
def isColimit (B : LowerSet P) :
    let Q := OriginalInitialFamilyCellTree.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T hObjects hMaps hFull
    let b := OriginalInitialFamilyComparison.comparison S orders hDirected hMono hRestrict
      hInitial hBelow hCover T hObjects hMaps hFull Y beta hBetas
    let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    IsColimit
      (@OriginalLowerComparisonCocone.cocone P P
        (order (pOrder := pOrder) S orders hDirected hMono hRestrict hBelow hCover).toPreorder
        pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
        f Q.diagram Y b L B) := by
  let ls := lower S orders hDirected hMono hRestrict hBelow hCover
  let gs := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
    hInitial hBelow hCover T
  let ho := InitialOrderCellTreeCompatibility.objects_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hObjects
  let hm := InitialOrderCellTreeCompatibility.maps_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T hMaps
  let bs := OriginalRefiningStageComparison.comparison S orders hDirected hMono hRestrict
    hInitial hBelow hCover T Y beta
  let hb := OriginalRefiningStageComparison.components_overlap S orders hDirected hMono
    hRestrict hInitial hBelow hCover T Y beta hBetas
  let f := wholeLabels S orders hDirected hMono hRestrict hBelow hCover
  let ds := OriginalLowerStagePieces.pieces S hMono B
  have hUnion := OriginalLowerStagePieces.pieces_union S hMono hCover B
  let hc := fun (i : I) (p : P) (hp : p ∈ ds.obj i) => hp.2
  let hu := fun i : I =>
    @OrderIsoLowerColimitTransport.isColimit
      (lower S orders hDirected hMono hRestrict hBelow hCover i) (S i) P
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i)
      (orders i) pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
      (stageIso S orders hDirected hMono hRestrict hInitial hBelow hCover i)
      (localLabels S orders hBelow i) (letI := orders i; (T i).diagram) Y (beta i) L
      (ds.obj i) (hLocal i (ds.obj i) inf_le_right)
  let pGlobal := order S orders hDirected hMono hRestrict hBelow hCover
  let fs := fun i : I => letI := pGlobal; (gs i).diagram
  let : IsDirectedOrder I := ⟨hDirected⟩
  have hUP := @InitialComparisonFilteredLowerColimit.isColimit P I P pGlobal
    (@Preorder.smallCategory I iOrder) (inferInstance : IsFiltered I)
    pOrder.toPreorder (Under X) (inferInstance : Category.{v} (Under X))
    ls fs hCover ho hm f Y bs hb L ds hc hu
  rw [hUnion] at hUP
  exact hUP

end CategoryTheory.SmallObject.OriginalInitialFamilyLowerColimits
