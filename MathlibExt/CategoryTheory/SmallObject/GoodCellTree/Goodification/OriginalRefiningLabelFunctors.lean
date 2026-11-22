/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellOrderDirectedUnion
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Literal original-label functors from actual refining cell orders

Both original and refining order dictionaries are explicit. The whole
and local comparison functors are identity on the actual original labels;
every map is the actual original precedence map. Their composition with
an original diagram retains that same original diagram and map function.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.OriginalRefiningLabelFunctors

open Limits LowerSetColimits InitialOrderFamilyGlue

variable {P I : Type w} [pOrder : PartialOrder P] [Preorder I]
  (S : I → LowerSet P) (orders : ∀ i : I, PartialOrder (S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hMono : Monotone S)
  (hRestrict : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i),
    @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩ ↔
      @LE.le (S j) (orders j).toLE ⟨a, hMono hij ha⟩ ⟨b, hMono hij hb⟩)
  (hBelow : ∀ (i : I) (a b : S i),
    @LE.le (S i) (orders i).toLE a b → a.1 ≤ b.1)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)

/-- The actual whole refining order keeps the literal original-label identity map. -/
def wholeLabels :
    @OrderHom P P (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder
      pOrder.toPreorder :=
  @OrderHom.mk P P (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder
    pOrder.toPreorder (fun p => p) (by
      intro a b h
      exact CellOrderDirectedUnion.unionLe_below (rel S orders) (rel_below S orders hBelow) h)

/-- Every local refining order keeps its original lower-subtype label inclusion. -/
def localLabels (i : I) : @OrderHom (S i) P (orders i).toPreorder pOrder.toPreorder :=
  @OrderHom.mk (S i) P (orders i).toPreorder pOrder.toPreorder (fun p => p.1)
    (by intro a b h; exact hBelow i a b h)

/-- The full whole original-label comparison functor keeps both actual order dictionaries. -/
def wholeFunctor :
    @Functor P
      (@Preorder.smallCategory P
        (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder)
      P (@Preorder.smallCategory P pOrder.toPreorder) :=
  @Monotone.functor P P
    (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder
    pOrder.toPreorder (fun p => p)
    (@OrderHom.monotone' P P
      (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder
      pOrder.toPreorder (wholeLabels S orders hDirected hMono hRestrict hBelow hCover))

/-- The full local original-label comparison functor uses the same original subtype function. -/
def localFunctor (i : I) :
    @Functor (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder)
      P (@Preorder.smallCategory P pOrder.toPreorder) :=
  @Monotone.functor (S i) P (orders i).toPreorder pOrder.toPreorder (fun p => p.1)
    (@OrderHom.monotone' (S i) P (orders i).toPreorder pOrder.toPreorder
      (localLabels S orders hBelow i))

/-- The whole label-object function is the literal identity on the original carrier. -/
theorem wholeFunctor_obj_function :
    @Functor.obj P
      (@Preorder.smallCategory P
        (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder)
      P (@Preorder.smallCategory P pOrder.toPreorder)
      (wholeFunctor S orders hDirected hMono hRestrict hBelow hCover) = id := rfl

omit [Preorder I] in
/-- Every complete local label-object function is the same original subtype inclusion. -/
theorem localFunctor_obj_function (i : I) :
    @Functor.obj (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder)
      P (@Preorder.smallCategory P pOrder.toPreorder) (localFunctor S orders hBelow i) =
        (fun p : S i => p.1) := rfl

variable {C : Type u} [cCategory : Category.{v} C] (Y : P ⥤ C)

/-- The complete original diagram is pulled through its actual whole original-label functor. -/
def wholeOriginalDiagram :
    @Functor P
      (@Preorder.smallCategory P
        (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder)
      C cCategory :=
  @Functor.comp P
    (@Preorder.smallCategory P
      (order S orders hDirected hMono hRestrict hBelow hCover).toPreorder)
    P (@Preorder.smallCategory P pOrder.toPreorder) C cCategory
    (wholeFunctor S orders hDirected hMono hRestrict hBelow hCover) Y

/-- Every complete actual local comparison keeps the same original diagram and original maps. -/
def localOriginalDiagram (i : I) :
    @Functor (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder) C cCategory :=
  @Functor.comp (S i) (@Preorder.smallCategory (S i) (orders i).toPreorder)
    P (@Preorder.smallCategory P pOrder.toPreorder) C cCategory
    (localFunctor S orders hBelow i) Y

end CategoryTheory.SmallObject.OriginalRefiningLabelFunctors
