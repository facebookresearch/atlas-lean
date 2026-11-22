/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyStageEquality
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Actual predecessor cocones from original initial-stage cell trees

The actual selected stage predecessor cocone is whiskered by its literal
predecessor-label order isomorphism and precomposed by the proved whole
diagram equality. This constructs the complete global predecessor colimit,
keeping its selected point and all original predecessor maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.InitialCellTreePredecessorGlue

open Limits LowerSetColimits InitialFunctorFamilyGlue
  InitialFunctorFamilyStageEquality

variable {P I : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (S : I → LowerSet P) (T : ∀ i : I, CellTree s X (P := S i))
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).vertex ⟨p, hi⟩ = (T j).vertex ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (T i).diagram.map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (T j).diagram.map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))

/-- The complete actual glued vertex diagram under the original root. -/
abbrev diagram : P ⥤ Under X :=
  functor S (fun i => (T i).diagram) hCover hObj hMap

/-- The actual old strict-predecessor cocone on the complete original label carrier. -/
abbrev localCocone (i : I) (p : P) (hp : p ∈ S i) :=
  ((T i).predecessor ⟨p, hp⟩).cocone.whisker
    (predecessorOrderIso S i p hp).symm.equivalence.functor

/-- Its actual old predecessor colimit survives the literal label order isomorphism. -/
def localIsColimit (i : I) (p : P) (hp : p ∈ S i) :
    IsColimit (localCocone S T i p hp) :=
  ((T i).predecessor ⟨p, hp⟩).isColimit.whiskerEquivalence
    (predecessorOrderIso S i p hp).symm.equivalence

/-- The full global predecessor cocone retains the same actual selected stage point. -/
abbrev predecessorCocone (i : I) (p : P) (hp : p ∈ S i) :
    Cocone (restriction (diagram S T hCover hObj hMap) (LowerSet.Iio p)) :=
  (Cocone.precompose (eqToHom
    (predecessorDiagram_eq S (fun i => (T i).diagram) hCover hObj hMap i p hp).symm)).obj
      (localCocone S T i p hp)

/-- Both actual diagram and index comparisons construct the global predecessor UP. -/
def predecessorIsColimit (i : I) (p : P) (hp : p ∈ S i) :
    IsColimit (predecessorCocone S T hCover hObj hMap i p hp) :=
  (IsColimit.precomposeHomEquiv
    (eqToIso (predecessorDiagram_eq S (fun i => (T i).diagram)
      hCover hObj hMap i p hp).symm) (localCocone S T i p hp)).symm
    (localIsColimit S T i p hp)

/-- The complete actual global predecessor data is constructed from the old stage cocone. -/
abbrev predecessor (i : I) (p : P) (hp : p ∈ S i) :
    ColimitCocone (restriction (diagram S T hCover hObj hMap) (LowerSet.Iio p)) :=
  ⟨predecessorCocone S T hCover hObj hMap i p hp,
    predecessorIsColimit S T hCover hObj hMap i p hp⟩

/-- The global predecessor point is precisely the original stage's selected under-object. -/
theorem predecessor_point (i : I) (p : P) (hp : p ∈ S i) :
    (predecessor S T hCover hObj hMap i p hp).cocone.pt =
      (T i).predecessorObj ⟨p, hp⟩ := rfl

/-- Every actual predecessor leg is the original stage leg with its actual object comparison. -/
theorem predecessor_leg (i : I) (p : P) (hp : p ∈ S i) (q : LowerSet.Iio p) :
    (predecessor S T hCover hObj hMap i p hp).cocone.ι.app q =
      eqToHom (obj_eq S (fun i => (T i).diagram) hCover hObj i q.1
        ((S i).lower' q.2.le hp)) ≫
      ((T i).predecessor ⟨p, hp⟩).cocone.ι.app
        ((predecessorOrderIso S i p hp).symm q) := by
  change (eqToHom _ : restriction (diagram S T hCover hObj hMap) (LowerSet.Iio p) ⟶
    (predecessorOrderIso S i p hp).symm.equivalence.functor ⋙
      restriction (T i).diagram (LowerSet.Iio (⟨p, hp⟩ : S i))).app q ≫ _ = _
  rw [eqToHom_app]
  rfl

/-- The complete global predecessor map is the actual original stage map into the same vertex. -/
theorem predecessorMap_eq (i : I) (p : P) (hp : p ∈ S i) :
    cellTreePredecessorMap (diagram S T hCover hObj hMap) p
      (predecessor S T hCover hObj hMap i p hp) =
    (T i).predecessorMap ⟨p, hp⟩ ≫
      eqToHom (obj_eq S (fun i => (T i).diagram) hCover hObj i p hp).symm := by
  apply (predecessor S T hCover hObj hMap i p hp).isColimit.hom_ext
  intro q
  rw [cellTreePredecessorMap_fac]
  have hm := (conj_eqToHom_iff_heq
    ((diagram S T hCover hObj hMap).map (homOfLE q.2.le))
    ((T i).diagram.map
      (homOfLE q.2.le :
        ((predecessorOrderIso S i p hp).symm q).1 ⟶ (⟨p, hp⟩ : S i)))
    (obj_eq S (fun i => (T i).diagram) hCover hObj i q.1 ((S i).lower' q.2.le hp))
    (obj_eq S (fun i => (T i).diagram) hCover hObj i p hp)).2
    (map_stage_heq S (fun i => (T i).diagram) hCover hObj hMap i _ hp
      (homOfLE q.2.le : q.1 ⟶ p))
  rw [← (T i).predecessorMap_fac ⟨p, hp⟩
    ((predecessorOrderIso S i p hp).symm q)] at hm
  have hLegComp := congrArg
    (fun l => l ≫ ((T i).predecessorMap ⟨p, hp⟩ ≫
      eqToHom (obj_eq S (fun i => (T i).diagram) hCover hObj i p hp).symm))
    (predecessor_leg S T hCover hObj hMap i p hp q)
  apply hm.trans
  apply Eq.trans _ hLegComp.symm
  let fq : (diagram S T hCover hObj hMap).obj q.1 ⟶
      (T i).vertex ((predecessorOrderIso S i p hp).symm q).1 :=
    eqToHom (obj_eq S (fun i => (T i).diagram) hCover hObj i q.1
      ((S i).lower' q.2.le hp))
  let lq := ((T i).predecessor ⟨p, hp⟩).cocone.ι.app
    ((predecessorOrderIso S i p hp).symm q)
  let vp := (T i).predecessorMap ⟨p, hp⟩
  let pq : (T i).vertex ⟨p, hp⟩ ⟶ (diagram S T hCover hObj hMap).obj p :=
    eqToHom (obj_eq S (fun i => (T i).diagram) hCover hObj i p hp).symm
  change fq ≫ (lq ≫ vp) ≫ pq = (fq ≫ lq) ≫ vp ≫ pq
  simp only [Category.assoc]

end CategoryTheory.SmallObject.InitialCellTreePredecessorGlue
