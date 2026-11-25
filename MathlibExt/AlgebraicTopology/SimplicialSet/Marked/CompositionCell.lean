/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
# The actual marked composition cell

The whole original two-simplex is unchanged. The source marks its two
short original edges, and the target additionally marks its long original
edge. The right lifting condition is exactly closure of the supplied mark
set under that actual composition triangle. This is an ordinary native
marked-cell condition, without a model or quasicategory premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original short edges of the standard composition triangle. -/
def compositionShortEdges : Set ((Δ[2] : SSet.{u}) _⦋1⦌) :=
  {SSet.yonedaEquiv (SSet.stdSimplex.δ (2 : Fin 3)),
    SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 3))}

/-- The original long edge of that same full triangle. -/
def compositionLongEdge : (Δ[2] : SSet.{u}) _⦋1⦌ := SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 3))

/-- The same original triangle with the two short edges marked. -/
def compositionCellSource : Marked.{u} := withEdges (Δ[2] : SSet.{u}) compositionShortEdges

/-- The same entire triangle with its long edge additionally marked. -/
def compositionCellTarget : Marked.{u} :=
  withEdges (Δ[2] : SSet.{u}) (insert compositionLongEdge compositionShortEdges)

/-- The original identity map adjoins only the long-edge marking. -/
def compositionCell : compositionCellSource.{u} ⟶ compositionCellTarget.{u} :=
  withEdgesInclusion (Set.subset_insert _ _)

/-- The whole underlying original triangle is unchanged. -/
@[simp]
theorem compositionCell_hom : compositionCell.{u}.hom = 𝟙 (Δ[2] : SSet.{u}) := rfl

/-- Adjoining this original marking is a native marked monomorphism. -/
theorem compositionCell_mono : Mono compositionCell.{u} := withEdgesInclusion_mono _

/-- The native composition cell lifts exactly when the original mark set contains every such long edge. -/
theorem compositionCell_rlp_iff {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B) :
    HasLiftingProperty compositionCell.{u} p ↔
      ∀ t : (Δ[2] : SSet.{u}) ⟶ Y.toSSet,
        t.app (op ⦋1⦌) (SSet.yonedaEquiv (SSet.stdSimplex.δ (2 : Fin 3))) ∈ Y.marking →
        t.app (op ⦋1⦌) (SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 3))) ∈ Y.marking →
        t.app (op ⦋1⦌) compositionLongEdge.{u} ∈ Y.marking := by
  constructor
  · intro hp t h₂ h₀
    let a : compositionCellSource.{u} ⟶ Y := ofWithEdges t (by
      intro e he
      rcases he with he | he
      · exact he ▸ h₂
      · exact he ▸ h₀)
    let b : compositionCellTarget.{u} ⟶ max B := toMax (t ≫ p.hom)
    let _ : HasLiftingProperty compositionCell.{u} p := hp
    have sq : CommSq a compositionCell.{u} p b := ⟨Hom.ext (Category.id_comp _).symm⟩
    have ht : sq.lift.hom = t := by
      let F : (Δ[2] : SSet.{u}) ⟶ Y.toSSet := sq.lift.hom
      have h : (𝟙 (Δ[2] : SSet.{u})) ≫ F = t := congrArg Hom.hom sq.fac_left
      exact (Category.id_comp F).symm.trans h
    have h := sq.lift.preserve (show compositionLongEdge.{u} ∈ compositionCellTarget.{u}.marking from
      Or.inr (Or.inl rfl))
    exact ht ▸ h
  · intro h
    refine ⟨fun {a b} sq => ?_⟩
    have h₂ := a.preserve (show SSet.yonedaEquiv (SSet.stdSimplex.δ (2 : Fin 3)) ∈
      compositionCellSource.{u}.marking from Or.inr (Or.inl rfl))
    have h₀ := a.preserve (show SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 3)) ∈
      compositionCellSource.{u}.marking from Or.inr (Or.inr rfl))
    let f : compositionCellTarget.{u} ⟶ Y := ofWithEdges a.hom (by
      intro e he
      rcases he with he | he
      · exact he ▸ h a.hom h₂ h₀
      · exact a.preserve (Or.inr he))
    have hb : f.hom ≫ p.hom = b.hom := by
      let F : (Δ[2] : SSet.{u}) ⟶ Y.toSSet := a.hom
      let G : (Δ[2] : SSet.{u}) ⟶ (max B).toSSet := b.hom
      have h' : F ≫ p.hom = (𝟙 (Δ[2] : SSet.{u})) ≫ G := congrArg Hom.hom sq.w
      exact h'.trans (Category.id_comp G)
    exact CommSq.HasLift.mk' ⟨f, Hom.ext (Category.id_comp _), Hom.ext hb⟩

end SSet.Marked
