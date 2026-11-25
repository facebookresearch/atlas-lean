/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointCells
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
# Marked endpoint lifts retain the original edges

The native endpoint lifting cells provide marked lifts of the entire
prescribed base edge. The target or source vertex is kept literally.
No inner-fibration or quasicategory hypothesis is needed for extracting
these actual marked edge lifts.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- A target-endpoint cell lift supplies a marked edge with the given target and whole base image. -/
theorem exists_marked_target_lift {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    (he : HasLiftingProperty cartesianEndpointCell.{u} p)
    (y : Y.toSSet _⦋0⦌) (b : (max B).toSSet _⦋0⦌)
    (e : Edge b (p.hom.app (op ⦋0⦌) y)) :
    ∃ (x : Y.toSSet _⦋0⦌) (f : Edge x y),
      f.edge ∈ Y.marking ∧ (f.map p.hom).edge = e.edge := by
  have hsq : SSet.yonedaEquiv.symm y ≫ p.hom =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq]
  obtain ⟨a, ht, hb⟩ := (cartesianEndpointCell_rlp_iff p).mp he
    (SSet.yonedaEquiv.symm y) (SSet.yonedaEquiv.symm e.edge) hsq
  let F : (Δ[1] : SSet.{u}) ⟶ Y.toSSet := a.hom
  let z := SSet.yonedaEquiv F
  have htarget : Y.toSSet.δ 0 z = y := by
    have ht' : SSet.stdSimplex.δ (0 : Fin 2) ≫ F = SSet.yonedaEquiv.symm y := ht
    change Y.toSSet.δ 0 (SSet.yonedaEquiv F) = y
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ht', Equiv.apply_symm_apply]
  let f : Edge (Y.toSSet.δ 1 z) y := Edge.mk z rfl htarget
  refine ⟨_, f, a.preserve (Set.mem_univ _), ?_⟩
  have hb' : F ≫ p.hom = SSet.yonedaEquiv.symm e.edge := hb
  change p.hom.app (op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
  rw [← SSet.yonedaEquiv_comp, hb', Equiv.apply_symm_apply]

/-- The source-endpoint cell supplies the dual marked lift with the entire original base edge. -/
theorem exists_marked_source_lift {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    (he : HasLiftingProperty cocartesianEndpointCell.{u} p)
    (x : Y.toSSet _⦋0⦌) (b : (max B).toSSet _⦋0⦌)
    (e : Edge (p.hom.app (op ⦋0⦌) x) b) :
    ∃ (y : Y.toSSet _⦋0⦌) (f : Edge x y),
      f.edge ∈ Y.marking ∧ (f.map p.hom).edge = e.edge := by
  have hsq : SSet.yonedaEquiv.symm x ≫ p.hom =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq]
  obtain ⟨a, hs, hb⟩ := (cocartesianEndpointCell_rlp_iff p).mp he
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm e.edge) hsq
  let F : (Δ[1] : SSet.{u}) ⟶ Y.toSSet := a.hom
  let z := SSet.yonedaEquiv F
  have hsource : Y.toSSet.δ 1 z = x := by
    have hs' : SSet.stdSimplex.δ (1 : Fin 2) ≫ F = SSet.yonedaEquiv.symm x := hs
    change Y.toSSet.δ 1 (SSet.yonedaEquiv F) = x
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hs', Equiv.apply_symm_apply]
  let f : Edge x (Y.toSSet.δ 0 z) := Edge.mk z hsource rfl
  refine ⟨_, f, a.preserve (Set.mem_univ _), ?_⟩
  have hb' : F ≫ p.hom = SSet.yonedaEquiv.symm e.edge := hb
  change p.hom.app (op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
  rw [← SSet.yonedaEquiv_comp, hb', Equiv.apply_symm_apply]

end SSet.Marked
