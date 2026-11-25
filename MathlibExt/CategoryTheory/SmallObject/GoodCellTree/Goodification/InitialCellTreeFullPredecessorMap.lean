/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialCellTreeFullCompatibility
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyStageEquality
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# Original predecessor-map preservation from the full actual cofans

The predecessor descender is derived from the actual full vertex diagram
and the original predecessor universal property. Full preservation of
the selected cofan proves preservation of that descender on every
containing stage, without a separate desired-map compatibility premise.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.InitialCellTreeFullPredecessorMap

open Limits LowerSetColimits InitialFunctorFamilyGlue
  InitialFunctorFamilyStageEquality InitialCellTreeFullCompatibility

variable {P I : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  [HasColimitsOfSize.{w, w} C] {A : Type t} {s : A → Arrow C} {X : C}
  (S : I → LowerSet P) (T : ∀ i : I, CellTree s X (P := S i))
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (T i).vertex ⟨p, hi⟩ = (T j).vertex ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (T i).diagram.map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (T j).diagram.map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))
  (hFull : Overlap S T)

include hFull in
/-- The actual full original cofan and diagram determine the same original predecessor map. -/
theorem predecessor_map_stage (i : I) (p : P) (hp : p ∈ S i) :
    (InitialCellTreeFullGlue.tree S T hCover hObj hMap hFull).predecessorMap p ≍
      (T i).predecessorMap ⟨p, hp⟩ := by
  let Q := InitialCellTreeFullGlue.tree S T hCover hObj hMap hFull
  let pp := (⟨p, hp⟩ : S i)
  have hPt : Q.predecessorObj p = (T i).predecessorObj pp :=
    predecessor_point_stage S T hCover hObj hMap hFull i p hp
  let hV : Q.vertex p = (T i).vertex pp :=
    obj_eq S (fun j => (T j).diagram) hCover hObj i p hp
  apply (conj_eqToHom_iff_heq (Q.predecessorMap p) ((T i).predecessorMap pp) hPt hV).1
  apply (cancel_mono (eqToHom hV)).1
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  apply (Q.predecessor p).isColimit.hom_ext
  intro q
  let qq := (⟨⟨q.1, (S i).lower' q.2.le hp⟩, q.2⟩ : LowerSet.Iio pp)
  let hQ : Q.vertex q.1 = (T i).vertex qq.1 :=
    obj_eq S (fun j => (T j).diagram) hCover hObj i q.1 ((S i).lower' q.2.le hp)
  have hLeg :
      (Q.predecessor p).cocone.ι.app q ≫ eqToHom hPt =
        eqToHom hQ ≫ ((T i).predecessor pp).cocone.ι.app qq := by
    have h := (conj_eqToHom_iff_heq ((Q.predecessor p).cocone.ι.app q)
      (((T i).predecessor pp).cocone.ι.app qq) hQ hPt).2
      (predecessor_leg_stage S T hCover hObj hMap hFull i p hp q)
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
      congrArg (fun m => m ≫ eqToHom hPt) h
  have hDiagram :
      Q.diagram.map (homOfLE q.2.le) ≫ eqToHom hV =
        eqToHom hQ ≫ (T i).diagram.map (homOfLE q.2.le : qq.1 ⟶ pp) := by
    have h := (conj_eqToHom_iff_heq (Q.diagram.map (homOfLE q.2.le))
      ((T i).diagram.map (homOfLE q.2.le : qq.1 ⟶ pp)) hQ hV).2
      (map_stage_heq S (fun j => (T j).diagram) hCover hObj hMap i qq.1.2 hp
        (homOfLE q.2.le : q.1 ⟶ p))
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
      congrArg (fun m => m ≫ eqToHom hV) h
  calc
    (Q.predecessor p).cocone.ι.app q ≫ (Q.predecessorMap p ≫ eqToHom hV) =
        ((Q.predecessor p).cocone.ι.app q ≫ Q.predecessorMap p) ≫ eqToHom hV :=
      (Category.assoc _ _ _).symm
    _ = Q.diagram.map (homOfLE q.2.le) ≫ eqToHom hV := by rw [Q.predecessorMap_fac]
    _ = eqToHom hQ ≫ (T i).diagram.map (homOfLE q.2.le : qq.1 ⟶ pp) := hDiagram
    _ = eqToHom hQ ≫
        (((T i).predecessor pp).cocone.ι.app qq ≫ (T i).predecessorMap pp) := by
      rw [(T i).predecessorMap_fac]
    _ = (eqToHom hQ ≫ ((T i).predecessor pp).cocone.ι.app qq) ≫
        (T i).predecessorMap pp := (Category.assoc _ _ _).symm
    _ = ((Q.predecessor p).cocone.ι.app q ≫ eqToHom hPt) ≫
        (T i).predecessorMap pp := by rw [hLeg]
    _ = (Q.predecessor p).cocone.ι.app q ≫
        (eqToHom hPt ≫ (T i).predecessorMap pp) := Category.assoc _ _ _

end CategoryTheory.SmallObject.InitialCellTreeFullPredecessorMap
