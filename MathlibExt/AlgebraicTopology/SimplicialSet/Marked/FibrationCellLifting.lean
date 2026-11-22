/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalRLP
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CocartesianCriticalRLP
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Fibration

/-!
# Actual marked cell lifts produce native relative fibrations

Inner cells give the original inner fibration. The endpoint cell supplies
an original marked lift of the entire base edge with its prescribed
endpoint. The critical cells make that actual marked lift Cartesian or
cocartesian. Thus these concrete cells prove the genuine native fibration
predicate, without assuming a quasicategory base or marked-model outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Original inner, target-endpoint and critical marked lifts prove a genuine Cartesian fibration. -/
theorem cartesianFibration_of_cell_lifting {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    (hi : ∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
      HasLiftingProperty (innerCell.{u} n i) p)
    (he : HasLiftingProperty cartesianEndpointCell.{u} p)
    (hc : ∀ n : ℕ, HasLiftingProperty (cartesianCriticalCell.{u} n) p) : CartesianFibration p.hom := by
  let _ : InnerFibration p.hom := (innerCell_rlp_iff p).mp hi
  refine { toInnerFibration := inferInstance, lift := ?_ }
  intro y b e
  have hsq : SSet.yonedaEquiv.symm y ≫ p.hom =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq]
  obtain ⟨f, ht, hb⟩ := (cartesianEndpointCell_rlp_iff p).mp he
    (SSet.yonedaEquiv.symm y) (SSet.yonedaEquiv.symm e.edge) hsq
  let F : (Δ[1] : SSet.{u}) ⟶ Y.toSSet := f.hom
  let z := SSet.yonedaEquiv F
  let x := Y.toSSet.δ 1 z
  have htarget : Y.toSSet.δ 0 z = y := by
    have ht' : SSet.stdSimplex.δ (0 : Fin 2) ≫ F = SSet.yonedaEquiv.symm y := ht
    change Y.toSSet.δ 0 (SSet.yonedaEquiv F) = y
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, ht', Equiv.apply_symm_apply]
  let a : Edge x y := Edge.mk z rfl htarget
  have hmap : (a.map p.hom).edge = e.edge := by
    have hb' : F ≫ p.hom = SSet.yonedaEquiv.symm e.edge := hb
    change p.hom.app (op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
    rw [← SSet.yonedaEquiv_comp, hb', Equiv.apply_symm_apply]
  have hsource : p.hom.app (op ⦋0⦌) x = b := by
    exact (a.map p.hom).src_eq.symm.trans
      ((congrArg (fun t => (max B).toSSet.δ 1 t) hmap).trans e.src_eq)
  have hmarked : z ∈ Y.marking := f.preserve (Set.mem_univ _)
  have hcart : CartesianEdge.IsPCartesian p.hom (SSet.yonedaEquiv.symm a.edge) :=
    (cartesianCriticalCell_rlp_iff p).mp hc z hmarked
  exact ⟨x, hsource, a, hcart, hmap⟩

/-- The source-endpoint and critical left cells prove the genuine original cocartesian fibration predicate. -/
theorem cocartesianFibration_of_cell_lifting {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    (hi : ∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
      HasLiftingProperty (innerCell.{u} n i) p)
    (he : HasLiftingProperty cocartesianEndpointCell.{u} p)
    (hc : ∀ n : ℕ, HasLiftingProperty (cocartesianCriticalCell.{u} n) p) : CocartesianFibration p.hom := by
  let _ : InnerFibration p.hom := (innerCell_rlp_iff p).mp hi
  refine { toInnerFibration := inferInstance, lift := ?_ }
  intro x b e
  have hsq : SSet.yonedaEquiv.symm x ≫ p.hom =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq]
  obtain ⟨f, hs, hb⟩ := (cocartesianEndpointCell_rlp_iff p).mp he
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm e.edge) hsq
  let F : (Δ[1] : SSet.{u}) ⟶ Y.toSSet := f.hom
  let z := SSet.yonedaEquiv F
  let y := Y.toSSet.δ 0 z
  have hsource : Y.toSSet.δ 1 z = x := by
    have hs' : SSet.stdSimplex.δ (1 : Fin 2) ≫ F = SSet.yonedaEquiv.symm x := hs
    change Y.toSSet.δ 1 (SSet.yonedaEquiv F) = x
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hs', Equiv.apply_symm_apply]
  let a : Edge x y := Edge.mk z hsource rfl
  have hmap : (a.map p.hom).edge = e.edge := by
    have hb' : F ≫ p.hom = SSet.yonedaEquiv.symm e.edge := hb
    change p.hom.app (op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
    rw [← SSet.yonedaEquiv_comp, hb', Equiv.apply_symm_apply]
  have htarget : p.hom.app (op ⦋0⦌) y = b := by
    exact (a.map p.hom).tgt_eq.symm.trans
      ((congrArg (fun t => (max B).toSSet.δ 0 t) hmap).trans e.tgt_eq)
  have hmarked : z ∈ Y.marking := f.preserve (Set.mem_univ _)
  have hcart : CocartesianEdge.IsPCocartesian p.hom (SSet.yonedaEquiv.symm a.edge) :=
    (cocartesianCriticalCell_rlp_iff p).mp hc z hmarked
  exact ⟨y, htarget, a, hcart, hmap⟩

end SSet.Marked
