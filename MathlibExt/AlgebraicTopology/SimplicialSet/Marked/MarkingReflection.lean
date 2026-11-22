/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.KanMarkCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval

/-!
# The native one-edge cell detects marking reflection

For maps between arbitrary original marked simplicial sets, the identity
interval cell from minimal to maximal marking lifts precisely when the
map reflects marking of every original edge. The interval is not assumed
Kan, and neither source nor target has a fibrancy hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original identity interval map adjoins the marking of its actual nondegenerate edge. -/
def edgeMarkCell : min (Δ[1] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) := kanMarkCell _

/-- This finite marking cell keeps every original interval simplex. -/
@[simp]
theorem edgeMarkCell_hom : edgeMarkCell.{u}.hom = 𝟙 (Δ[1] : SSet.{u}) := rfl

/-- The native one-edge marking cell is a genuine marked monomorphism. -/
theorem edgeMarkCell_mono : Mono edgeMarkCell.{u} := kanMarkCell_mono _

/-- The original one-edge cell lifts exactly when the supplied marked map reflects every marking. -/
theorem edgeMarkCell_rlp_iff {X Y : Marked.{u}} (p : X ⟶ Y) :
    HasLiftingProperty edgeMarkCell.{u} p ↔
      ∀ e : X.toSSet _⦋1⦌, p.hom.app (op ⦋1⦌) e ∈ Y.marking → e ∈ X.marking := by
  constructor
  · intro hp e he
    let a : min (Δ[1] : SSet.{u}) ⟶ X := ofMin (yonedaEquiv.symm e)
    let b := intervalMapOfMarkedEdge (p.hom.app (op ⦋1⦌) e) he
    let _ : HasLiftingProperty edgeMarkCell.{u} p := hp
    have sq : CommSq a edgeMarkCell.{u} p b := ⟨Hom.ext (by
      change yonedaEquiv.symm e ≫ p.hom = (𝟙 (Δ[1] : SSet.{u})) ≫
        yonedaEquiv.symm (p.hom.app (op ⦋1⦌) e)
      rw [Category.id_comp, yonedaEquiv_symm_comp])⟩
    have hf : sq.lift.hom = yonedaEquiv.symm e := by
      let F : (Δ[1] : SSet.{u}) ⟶ X.toSSet := sq.lift.hom
      have h : (𝟙 (Δ[1] : SSet.{u})) ≫ F = yonedaEquiv.symm e := congrArg Hom.hom sq.fac_left
      exact (Category.id_comp F).symm.trans h
    have hm : yonedaEquiv sq.lift.hom ∈ X.marking := (maxIntervalHomEquiv X sq.lift).property
    rw [hf, Equiv.apply_symm_apply] at hm
    exact hm
  · intro hr
    refine ⟨fun {a b} sq => ?_⟩
    let A : (Δ[1] : SSet.{u}) ⟶ X.toSSet := a.hom
    let G : (Δ[1] : SSet.{u}) ⟶ Y.toSSet := b.hom
    have hp : A ≫ p.hom = G := by
      have h : A ≫ p.hom = (𝟙 (Δ[1] : SSet.{u})) ≫ G := congrArg Hom.hom sq.w
      exact h.trans (Category.id_comp G)
    have hm : yonedaEquiv A ∈ X.marking := hr _ (by
      have h : p.hom.app (op ⦋1⦌) (yonedaEquiv A) = yonedaEquiv G :=
        (yonedaEquiv_comp A p.hom).symm.trans (congrArg yonedaEquiv hp)
      exact h.symm ▸ (maxIntervalHomEquiv Y b).property)
    let f := intervalMapOfMarkedEdge (yonedaEquiv A) hm
    refine CommSq.HasLift.mk' ⟨f, Hom.ext ?_, Hom.ext ?_⟩
    · change (𝟙 (Δ[1] : SSet.{u})) ≫ yonedaEquiv.symm (yonedaEquiv A) = A
      exact (Category.id_comp _).trans (Equiv.symm_apply_apply _ _)
    · change yonedaEquiv.symm (yonedaEquiv A) ≫ p.hom = G
      exact (congrArg (fun t => t ≫ p.hom) (Equiv.symm_apply_apply yonedaEquiv A)).trans hp

end SSet.Marked
