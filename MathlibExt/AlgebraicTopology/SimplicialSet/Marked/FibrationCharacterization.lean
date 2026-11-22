/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrationCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CanonicalCellLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingCompleteness

/-!
# The actual small cell class detects the intrinsic marked fibrations

Over an arbitrary quasicategory base, the genuine small family detects
exactly the original Cartesian or cocartesian fibrations with precisely
their original relative edges marked. The base need not be Kan. Every
edge, endpoint and whole critical/composition simplex is retained.
This is a characterization of the actual testing right class; construction
of a marked weak-equivalence class and model remains separate.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The actual small Cartesian right class is precisely the native fibration and its exact intrinsic marking. -/
theorem cartesianCells_rlp_iff_cartesianObjects {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B) [Quasicategory B] :
    cartesianCells.{u}.rlp p ↔ cartesianObjects B (Over.mk p) := by
  let _ : Quasicategory (max B).toSSet := by
    change Quasicategory B
    infer_instance
  constructor
  · intro hp
    obtain ⟨hi, hc, he, ht, hk⟩ := (cartesianCells_rlp_iff p).mp hp
    let _ : InnerFibration p.hom := (innerCell_rlp_iff p).mp hi
    let _ : Quasicategory Y.toSSet := quasicategory_of_innerFibration p.hom
    refine ⟨cartesianFibration_of_cell_lifting p hi he hc, ?_⟩
    intro e
    exact ⟨(cartesianCriticalCell_rlp_iff p).mp hc e,
      cartesian_mem_marking_of_cells p he hc ht ((equivalenceMarkCell_rlp_iff p).mp hk) e⟩
  · rintro ⟨hfib, hm⟩
    let _ : CartesianFibration p.hom := hfib
    apply (cartesianCells_rlp_iff p).mpr
    refine ⟨(innerCell_rlp_iff p).mpr inferInstance,
      (cartesianCriticalCell_rlp_iff p).mpr (fun e he => (hm e).mp he),
      cartesianEndpointCell_of_cartesianFibration p (fun e he => (hm e).mpr he), ?_, ?_⟩
    · apply (compositionCell_rlp_iff p).mpr
      intro t h₂ h₀
      have h₂' := (hm _).mp h₂
      have h₀' := (hm _).mp h₀
      apply (hm _).mpr
      change CartesianEdge.IsPCartesian p.hom (yonedaEquiv.symm
        (t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3)))))
      rw [← yonedaEquiv_comp, Equiv.symm_apply_apply] at h₂' h₀' ⊢
      exact (CartesianEdge.isPCartesian_face_two_iff_face_one p.hom t h₀').mp h₂'
    · let _ : Quasicategory Y.toSSet := quasicategory_of_innerFibration p.hom
      apply (equivalenceMarkCell_rlp_iff p).mpr
      intro e he
      apply (hm e).mpr
      apply CartesianEdge.isPCartesian_of_isEquivalence p.hom _
      exact he.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv e).symm

/-- The same actual small index detects precisely the original cocartesian fibration and marking. -/
theorem cocartesianCells_rlp_iff_cocartesianObjects {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B) [Quasicategory B] :
    cocartesianCells.{u}.rlp p ↔ cocartesianObjects B (Over.mk p) := by
  let _ : Quasicategory (max B).toSSet := by
    change Quasicategory B
    infer_instance
  constructor
  · intro hp
    obtain ⟨hi, hc, he, ht, hk⟩ := (cocartesianCells_rlp_iff p).mp hp
    let _ : InnerFibration p.hom := (innerCell_rlp_iff p).mp hi
    let _ : Quasicategory Y.toSSet := quasicategory_of_innerFibration p.hom
    refine ⟨cocartesianFibration_of_cell_lifting p hi he hc, ?_⟩
    intro e
    exact ⟨(cocartesianCriticalCell_rlp_iff p).mp hc e,
      cocartesian_mem_marking_of_cells p he hc ht ((equivalenceMarkCell_rlp_iff p).mp hk) e⟩
  · rintro ⟨hfib, hm⟩
    let _ : CocartesianFibration p.hom := hfib
    apply (cocartesianCells_rlp_iff p).mpr
    refine ⟨(innerCell_rlp_iff p).mpr inferInstance,
      (cocartesianCriticalCell_rlp_iff p).mpr (fun e he => (hm e).mp he),
      cocartesianEndpointCell_of_cocartesianFibration p (fun e he => (hm e).mpr he), ?_, ?_⟩
    · apply (compositionCell_rlp_iff p).mpr
      intro t h₂ h₀
      have h₂' := (hm _).mp h₂
      have h₀' := (hm _).mp h₀
      apply (hm _).mpr
      change CocartesianEdge.IsPCocartesian p.hom (yonedaEquiv.symm
        (t.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3)))))
      rw [← yonedaEquiv_comp, Equiv.symm_apply_apply] at h₂' h₀' ⊢
      exact (CocartesianEdge.isPCocartesian_face_zero_iff_face_one p.hom t h₂').mp h₀'
    · let _ : Quasicategory Y.toSSet := quasicategory_of_innerFibration p.hom
      apply (equivalenceMarkCell_rlp_iff p).mpr
      intro e he
      apply (hm e).mpr
      apply CocartesianEdge.isPCocartesian_of_isEquivalence p.hom _
      exact he.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv e).symm

/-- The original canonical Cartesian projection belongs to the actual small right class. -/
theorem cartesianCells_cartesianProjection {E B : SSet.{u}} (p : E ⟶ B)
    [CartesianFibration p] [Quasicategory B] : cartesianCells.{u}.rlp (cartesianProjection p) :=
  (cartesianCells_rlp_iff_cartesianObjects (cartesianProjection p)).mpr
    ⟨by change CartesianFibration p; infer_instance, fun _ => Iff.rfl⟩

/-- The native canonical cocartesian projection satisfies the dual small testing class. -/
theorem cocartesianCells_cocartesianProjection {E B : SSet.{u}} (p : E ⟶ B)
    [CocartesianFibration p] [Quasicategory B] : cocartesianCells.{u}.rlp (cocartesianProjection p) :=
  (cocartesianCells_rlp_iff_cocartesianObjects (cocartesianProjection p)).mpr
    ⟨by change CocartesianFibration p; infer_instance, fun _ => Iff.rfl⟩

end SSet.Marked
