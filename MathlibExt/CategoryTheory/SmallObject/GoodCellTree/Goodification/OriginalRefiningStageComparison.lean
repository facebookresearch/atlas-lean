/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningLabelFunctors
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningStageDiagram
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Actual original natural comparisons on reindexed refining stages

The actual old stage natural transformation is whiskered by the same
literal original-label order isomorphism. The proved full original diagram
equality identifies its target with the actual original whole diagram
restricted to that stage. All original component functions are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalRefiningStageComparison

open Limits LowerSetColimits InitialOrderFamilyGlue OriginalRefiningLabelFunctors
  OriginalRefiningStageDiagram

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
  {C : Type u} [cCategory : Category.{v} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : ∀ i : I, letI := orders i; CellTree s X (P := S i))
  (Y : P ⥤ Under X)
  (beta : ∀ i : I,
    letI := orders i
    letI : Preorder (S i) := (orders i).toPreorder
    (T i).diagram ⟶ localOriginalDiagram S orders hBelow Y i)

/-- The actual complete original stage comparison is the whiskered old natural transformation. -/
def comparison (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T i
    let Z := wholeOriginalDiagram S orders hDirected hMono hRestrict hBelow hCover Y
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    G.diagram ⟶ restriction Z (L i) :=
  @Functor.whiskerLeft (lower S orders hDirected hMono hRestrict hBelow hCover i)
    (@Preorder.smallCategory (lower S orders hDirected hMono hRestrict hBelow hCover i)
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder)
    (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder)
    (Under X) (inferInstance : Category.{v} (Under X))
    (stageReindexFunctor S orders hDirected hMono hRestrict hInitial hBelow hCover i)
    (letI := orders i; (T i).diagram) (localOriginalDiagram S orders hBelow Y i) (beta i)

/-- The complete actual reindexed component function is the same original stage function. -/
theorem comparison_component (i : I) (p : P) (hp : p ∈ S i) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let b := comparison S orders hDirected hMono hRestrict hInitial hBelow hCover T Y beta i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    b.app (⟨p, hp⟩ : L i) =
      (letI := orders i
       letI : Preorder (S i) := (orders i).toPreorder
       (beta i).app ⟨p, hp⟩) := rfl

variable
  (hBetas : ∀ (i j : I) (_ : i ≤ j) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (letI := orders i
     letI : Preorder (S i) := (orders i).toPreorder
     (beta i).app ⟨p, hi⟩) ≍
    (letI := orders j
     letI : Preorder (S j) := (orders j).toPreorder
     (beta j).app ⟨p, hj⟩))

include hBetas in
/-- A real common original stage proves full reindexed component compatibility. -/
theorem components_overlap (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let b := comparison S orders hDirected hMono hRestrict hInitial hBelow hCover T Y beta
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    (b i).app (⟨p, hi⟩ : L i) ≍ (b j).app (⟨p, hj⟩ : L j) := by
  obtain ⟨k, hik, hjk⟩ := hDirected i j
  exact (hBetas i k hik p hi (hMono hik hi)).trans
    (hBetas j k hjk p hj (hMono hjk hj)).symm

end CategoryTheory.SmallObject.OriginalRefiningStageComparison
