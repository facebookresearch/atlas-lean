/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.ActualCoconeColimitTransport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyStageEquality
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorComparisonGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Actual original lower-colimit UPs at containing initial stages

A lower preimage contained in a real original stage has its complete
diagram equality with that stage's same original lower preimage. The
actual global/stage component comparison then transports the genuine
stage lower-colimit UP to the complete whole lower-comparison cocone.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.InitialComparisonLowerColimit

open Limits LowerSetColimits InitialFunctorFamilyGlue InitialFunctorFamilyStageEquality

variable {P I Q : Type w} [PartialOrder P] [Preorder Q]
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
  (L : LowerSetColimitData Y)

/-- The actual stage original-label map is the same original order map on its original subtype. -/
def stageLabels (i : I) : S i →o Q where
  toFun p := f p.1
  monotone' := by intro a b h; exact f.monotone h

variable (i : I) (D : LowerSet Q) (hD : ∀ p : P, f p ∈ D → p ∈ S i)

/-- The whole original lower preimage and its actual containing stage retain the same labels. -/
def carrierIso :
    OriginalLowerComparisonCocone.carrier f D ≃o
      OriginalLowerComparisonCocone.carrier (stageLabels S f i) D where
  toFun p := ⟨⟨p.1, hD p.1 p.2⟩, p.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Both whole lower diagrams retain the same complete original object and map functions. -/
theorem diagram_eq :
    restriction (functor S F hCover hObj hMap) (OriginalLowerComparisonCocone.carrier f D) =
      (carrierIso S f i D hD).equivalence.functor ⋙
        restriction (F i) (OriginalLowerComparisonCocone.carrier (stageLabels S f i) D) := by
  rw [← stage_eq S F hCover hObj hMap i]
  rfl

/-- The actual global and stage lower-comparison legs retain their same complete original maps. -/
theorem legs_heq (p : OriginalLowerComparisonCocone.carrier f D) :
    (OriginalLowerComparisonCocone.cocone f
      (functor S F hCover hObj hMap) Y
      (InitialFunctorComparisonGlue.comparison S F hCover hObj hMap f Y beta hBeta) L D).ι.app p ≍
    ((OriginalLowerComparisonCocone.cocone (stageLabels S f i) (F i) Y (beta i) L D).whisker
      (carrierIso S f i D hD).equivalence.functor).ι.app p := by
  exact heq_comp (obj_eq S F hCover hObj i p.1 (hD p.1 p.2)) rfl rfl
    (InitialFunctorComparisonGlue.component_heq S F hCover hObj f Y beta hBeta
      i p.1 (hD p.1 p.2)) HEq.rfl

/-- An actual containing-stage UP proves the whole original lower-colimit UP. -/
def isColimit
    (hLocal : IsColimit
      (OriginalLowerComparisonCocone.cocone (stageLabels S f i) (F i) Y (beta i) L D)) :
    IsColimit
      (OriginalLowerComparisonCocone.cocone f
        (functor S F hCover hObj hMap) Y
        (InitialFunctorComparisonGlue.comparison S F hCover hObj hMap f Y beta hBeta) L D) :=
  ActualCoconeColimitTransport.isColimit (diagram_eq S F hCover hObj hMap f i D hD)
    (OriginalLowerComparisonCocone.cocone f
      (functor S F hCover hObj hMap) Y
      (InitialFunctorComparisonGlue.comparison S F hCover hObj hMap f Y beta hBeta) L D)
    ((OriginalLowerComparisonCocone.cocone (stageLabels S f i) (F i) Y (beta i) L D).whisker
      (carrierIso S f i D hD).equivalence.functor)
    rfl (legs_heq S F hCover hObj hMap f Y beta hBeta L i D hD)
    (hLocal.whiskerEquivalence (carrierIso S f i D hD).equivalence)

end CategoryTheory.SmallObject.InitialComparisonLowerColimit
