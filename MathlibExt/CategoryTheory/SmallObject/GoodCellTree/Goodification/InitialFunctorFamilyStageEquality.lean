/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Actual stage restriction equality for the glued original vertex functor

The actual global diagram restricts to each original stage diagram as a
whole functor, including every original map. An old vertex's entire strict
predecessor diagram therefore has the original stage diagram after the
literal predecessor-label order isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.InitialFunctorFamilyStageEquality

open Limits LowerSetColimits InitialFunctorFamilyGlue

variable {P I : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  (S : I → LowerSet P) (F : ∀ i : I, S i ⥤ C)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (F i).obj ⟨p, hi⟩ = (F j).obj ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (F i).map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (F j).map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))

/-- The whole actual original stage restriction retains every original object and map. -/
theorem stage_eq (i : I) :
    restriction (functor S F hCover hObj hMap) (S i) = F i := by
  apply Functor.hext
  · intro p
    exact obj_eq S F hCover hObj i p.1 p.2
  · intro p q h
    exact map_stage_heq S F hCover hObj hMap i p.2 q.2 (homOfLE (leOfHom h))

/-- The original lower-stage inclusion keeps the full original strict predecessor carrier. -/
abbrev predecessorOrderIso (i : I) (p : P) (hp : p ∈ S i) :
    LowerSet.Iio (⟨p, hp⟩ : S i) ≃o LowerSet.Iio p :=
  CellTreeLowerRestriction.predecessorOrderIso (S i) ⟨p, hp⟩

/-- The whole strict predecessor diagram retains the actual original stage and labels. -/
theorem predecessorDiagram_eq (i : I) (p : P) (hp : p ∈ S i) :
    (predecessorOrderIso S i p hp).symm.equivalence.functor ⋙
        restriction (F i) (LowerSet.Iio (⟨p, hp⟩ : S i)) =
      restriction (functor S F hCover hObj hMap) (LowerSet.Iio p) := by
  rw [← stage_eq S F hCover hObj hMap i]
  rfl

end CategoryTheory.SmallObject.InitialFunctorFamilyStageEquality
