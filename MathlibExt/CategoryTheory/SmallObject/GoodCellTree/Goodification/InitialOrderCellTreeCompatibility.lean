/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellOrderDirectedUnion
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Actual whole/local diagram compatibility of original refining stages

Directedness turns the actual ordered initial-stage object/map
compatibility into full overlap compatibility. Reindexing uses the same
original labels and complete map functions. These are the derived
compatibility proofs used by the actual whole-tree gluing constructor.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.InitialOrderCellTreeCompatibility

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
  {C : Type u} [Category.{v} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : ∀ i : I, letI := orders i; CellTree s X (P := S i))

/-- The actual reindexed original stage map is the same full original local map. -/
theorem tree_map_heq (i : I) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i)
    (hab : CellOrderDirectedUnion.unionLe (rel S orders) a b) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T i
    let localHab := (le_at_stage S orders hDirected hMono hRestrict hInitial i a b ha hb).1 hab
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    G.diagram.map (homOfLE hab : (⟨a, ha⟩ : L i) ⟶ ⟨b, hb⟩) ≍
      (letI := orders i
       letI : Preorder (S i) := (orders i).toPreorder
       (T i).diagram.map (homOfLE localHab : (⟨a, ha⟩ : S i) ⟶ ⟨b, hb⟩)) := HEq.rfl

variable
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

include hObjects in
/-- A genuine common original stage proves complete reindexed overlap object compatibility. -/
theorem objects_overlap (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    (G i).vertex (⟨p, hi⟩ : L i) = (G j).vertex (⟨p, hj⟩ : L j) := by
  obtain ⟨k, hik, hjk⟩ := hDirected i j
  exact (hObjects i k hik p hi (hMono hik hi)).trans
    (hObjects j k hjk p hj (hMono hjk hj)).symm

include hMaps in
/-- Actual common-stage maps prove the complete original reindexed overlap Hom compatibility. -/
theorem maps_overlap (i j : I) (a b : P)
    (hai : a ∈ S i) (hbi : b ∈ S i) (haj : a ∈ S j) (hbj : b ∈ S j)
    (hab : CellOrderDirectedUnion.unionLe (rel S orders) a b) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    (G i).diagram.map (homOfLE hab : (⟨a, hai⟩ : L i) ⟶ ⟨b, hbi⟩) ≍
      (G j).diagram.map (homOfLE hab : (⟨a, haj⟩ : L j) ⟶ ⟨b, hbj⟩) := by
  obtain ⟨k, hik, hjk⟩ := hDirected i j
  have hi := (le_at_stage S orders hDirected hMono hRestrict hInitial i a b hai hbi).1 hab
  have hj := (le_at_stage S orders hDirected hMono hRestrict hInitial j a b haj hbj).1 hab
  exact (tree_map_heq S orders hDirected hMono hRestrict hInitial hBelow hCover
    T i a b hai hbi hab).trans
    (((hMaps i k hik a b hai hbi hi).trans
      (hMaps j k hjk a b haj hbj hj).symm).trans
      (tree_map_heq S orders hDirected hMono hRestrict hInitial hBelow hCover
        T j a b haj hbj hab).symm)

end CategoryTheory.SmallObject.InitialOrderCellTreeCompatibility
