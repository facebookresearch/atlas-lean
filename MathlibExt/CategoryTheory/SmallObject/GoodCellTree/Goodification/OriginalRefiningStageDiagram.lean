/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningLabelFunctors
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Whole original diagram equality across actual refining stages

The literal original stage order isomorphism identifies both complete
original-label functors. Composing the same original diagram gives an
equality of whole original object and map functions, with all order and
category dictionaries retained explicitly.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.OriginalRefiningStageDiagram

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

/-- The whole actual reindexing functor uses the literal original stage-label order isomorphism. -/
def stageReindexFunctor (i : I) :
    @Functor (lower S orders hDirected hMono hRestrict hBelow hCover i)
      (@Preorder.smallCategory (lower S orders hDirected hMono hRestrict hBelow hCover i)
        (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder)
      (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder) :=
  @Equivalence.functor (lower S orders hDirected hMono hRestrict hBelow hCover i) (S i)
    (@Preorder.smallCategory (lower S orders hDirected hMono hRestrict hBelow hCover i)
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder)
    (@Preorder.smallCategory (S i) (orders i).toPreorder)
    (@OrderIso.equivalence (lower S orders hDirected hMono hRestrict hBelow hCover i) (S i)
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder
      (orders i).toPreorder
      (stageIso S orders hDirected hMono hRestrict hInitial hBelow hCover i))

/-- The complete actual stage original-label functor keeps both original label functions. -/
def stageOriginalFunctor (i : I) :
    @Functor (lower S orders hDirected hMono hRestrict hBelow hCover i)
      (@Preorder.smallCategory (lower S orders hDirected hMono hRestrict hBelow hCover i)
        (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder)
      P (@Preorder.smallCategory P pOrder.toPreorder) :=
  @Functor.comp (lower S orders hDirected hMono hRestrict hBelow hCover i)
    (@Preorder.smallCategory (lower S orders hDirected hMono hRestrict hBelow hCover i)
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder)
    (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder)
    P (@Preorder.smallCategory P pOrder.toPreorder)
    (stageReindexFunctor S orders hDirected hMono hRestrict hInitial hBelow hCover i)
    (localFunctor S orders hBelow i)

/-- Both full original stage-label functors have identical actual object and Hom functions. -/
theorem stageOriginalFunctor_eq (i : I) :
    stageOriginalFunctor S orders hDirected hMono hRestrict hInitial hBelow hCover i =
      @restriction P (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder
        P (@Preorder.smallCategory P pOrder.toPreorder)
        (wholeFunctor S orders hDirected hMono hRestrict hBelow hCover)
        (lower S orders hDirected hMono hRestrict hBelow hCover i) := rfl

variable {C : Type u} [cCategory : Category.{v} C] (Y : P ⥤ C)

/-- The complete original local diagram is reindexed by its same original stage label function. -/
def stageOriginalDiagram (i : I) :
    @Functor (lower S orders hDirected hMono hRestrict hBelow hCover i)
      (@Preorder.smallCategory (lower S orders hDirected hMono hRestrict hBelow hCover i)
        (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder)
      C cCategory :=
  @Functor.comp (lower S orders hDirected hMono hRestrict hBelow hCover i)
    (@Preorder.smallCategory (lower S orders hDirected hMono hRestrict hBelow hCover i)
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toPreorder)
    (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder)
    C cCategory
    (stageReindexFunctor S orders hDirected hMono hRestrict hInitial hBelow hCover i)
    (localOriginalDiagram S orders hBelow Y i)

/-- The whole original stage diagram retains its complete original objects and maps. -/
theorem stageOriginalDiagram_eq (i : I) :
    stageOriginalDiagram S orders hDirected hMono hRestrict hInitial hBelow hCover Y i =
      @restriction P (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder
        C cCategory (wholeOriginalDiagram S orders hDirected hMono hRestrict hBelow hCover Y)
        (lower S orders hDirected hMono hRestrict hBelow hCover i) := rfl

end CategoryTheory.SmallObject.OriginalRefiningStageDiagram
