/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.FilteredOriginalLowerColimit
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialComparisonLowerColimit
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorComparisonGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Original lower-colimit invariants for actual filtered initial-stage unions

Actual containing-stage lower-colimit universal properties and the
original filtered lower-set diagram construct the whole invariant.
Every stage carrier, original component, original lower cocone and
filtered-union map is retained through the same full comparison functor.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.InitialComparisonFilteredLowerColimit

open Limits LowerSetColimits InitialFunctorFamilyGlue

variable {P I Q : Type w} [PartialOrder P] [Category.{w} I] [IsFiltered I] [Preorder Q]
  {C : Type u} [Category.{v} C]
  (S : I → LowerSet P) (F : ∀ i : I, S i ⥤ C)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (F i).obj ⟨p, hi⟩ = (F j).obj ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (F i).map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (F j).map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))
  (f : P →o Q) (Y : Q ⥤ C)
  (beta : ∀ i : I, F i ⟶ restriction (f.monotone.functor ⋙ Y) (S i))
  (hBeta : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (beta i).app ⟨p, hi⟩ ≍ (beta j).app ⟨p, hj⟩)
  (L : LowerSetColimitData Y) (D : I ⥤ LowerSet Q)
  (hContaining : ∀ (i : I) (p : P), f p ∈ D.obj i → p ∈ S i)

/-- Actual original local UPs and original filtered maps construct the whole lower invariant. -/
def isColimit
    (hLocal : ∀ i : I,
      IsColimit
        (OriginalLowerComparisonCocone.cocone
          (InitialComparisonLowerColimit.stageLabels S f i) (F i) Y (beta i) L (D.obj i))) :
    IsColimit
      (OriginalLowerComparisonCocone.cocone f (functor S F hCover hObj hMap) Y
        (InitialFunctorComparisonGlue.comparison S F hCover hObj hMap f Y beta hBeta) L
        (FilteredOriginalLowerColimit.union D)) :=
  FilteredOriginalLowerColimit.wholeIsColimit f (functor S F hCover hObj hMap) Y
    (InitialFunctorComparisonGlue.comparison S F hCover hObj hMap f Y beta hBeta) L D
    (fun i => InitialComparisonLowerColimit.isColimit S F hCover hObj hMap f Y beta hBeta
      L i (D.obj i) (hContaining i) (hLocal i))

end CategoryTheory.SmallObject.InitialComparisonFilteredLowerColimit
