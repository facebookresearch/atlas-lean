/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrationCellLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CompositionCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EquivalenceDetector
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Triangle
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.Triangle

/-!
# Actual intrinsic fibrations lift the native marked cells

The original fibration supplies the whole prescribed edge lift, whose
intrinsic marking yields the native marked interval map. Composition uses
the proved original two-simplex calculus. Inner and critical lifting are
their existing literal criteria, and the one fixed Kan marking detector
lifts by the original groupoidal-map theorem. These are actual lifting
proofs for the supplied carrier, not marked-model assumptions.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- A genuine Cartesian fibration with its actual Cartesian edges marked lifts the target-endpoint cell. -/
theorem cartesianEndpointCell_of_cartesianFibration {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B) [CartesianFibration p.hom]
    (hm : ∀ e : Y.toSSet _⦋1⦌,
      CartesianEdge.IsPCartesian p.hom (yonedaEquiv.symm e) → e ∈ Y.marking) :
    HasLiftingProperty cartesianEndpointCell.{u} p := by
  apply (cartesianEndpointCell_rlp_iff p).mpr
  intro a b hab
  let y := yonedaEquiv a
  let b' : (Δ[1] : SSet.{u}) ⟶ (max B).toSSet := b
  let z : (max B).toSSet _⦋1⦌ := yonedaEquiv b'
  have htarget : (max B).toSSet.δ 0 z = p.hom.app (op ⦋0⦌) y := by
    have hab' : a ≫ p.hom = stdSimplex.δ (0 : Fin 2) ≫ b' := hab
    have h := congrArg yonedaEquiv hab'
    rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp] at h
    exact h.symm
  let e : Edge ((max B).toSSet.δ 1 z) (p.hom.app (op ⦋0⦌) y) := Edge.mk z rfl htarget
  obtain ⟨x, hx, c, hc, hmap⟩ := CartesianFibration.lift (p := p.hom) y _ e
  let f := intervalMapOfMarkedEdge c.edge (hm c.edge hc)
  refine ⟨f, ?_, ?_⟩
  · change stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm c.edge = a
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, c.tgt_eq, Equiv.symm_apply_apply]
  · change yonedaEquiv.symm c.edge ≫ p.hom = b'
    rw [yonedaEquiv_symm_comp, ← Edge.map_edge, hmap]
    change yonedaEquiv.symm (yonedaEquiv b') = b'
    exact Equiv.symm_apply_apply _ _

/-- The native cocartesian source-edge lift gives the corresponding fully marked interval lift. -/
theorem cocartesianEndpointCell_of_cocartesianFibration {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B) [CocartesianFibration p.hom]
    (hm : ∀ e : Y.toSSet _⦋1⦌,
      CocartesianEdge.IsPCocartesian p.hom (yonedaEquiv.symm e) → e ∈ Y.marking) :
    HasLiftingProperty cocartesianEndpointCell.{u} p := by
  apply (cocartesianEndpointCell_rlp_iff p).mpr
  intro a b hab
  let x := yonedaEquiv a
  let b' : (Δ[1] : SSet.{u}) ⟶ (max B).toSSet := b
  let z : (max B).toSSet _⦋1⦌ := yonedaEquiv b'
  have hsource : (max B).toSSet.δ 1 z = p.hom.app (op ⦋0⦌) x := by
    have hab' : a ≫ p.hom = stdSimplex.δ (1 : Fin 2) ≫ b' := hab
    have h := congrArg yonedaEquiv hab'
    rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp] at h
    exact h.symm
  let e : Edge (p.hom.app (op ⦋0⦌) x) ((max B).toSSet.δ 0 z) := Edge.mk z hsource rfl
  obtain ⟨y, hy, c, hc, hmap⟩ := CocartesianFibration.lift (p := p.hom) x _ e
  let f := intervalMapOfMarkedEdge c.edge (hm c.edge hc)
  refine ⟨f, ?_, ?_⟩
  · change stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm c.edge = a
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, c.src_eq, Equiv.symm_apply_apply]
  · change yonedaEquiv.symm c.edge ≫ p.hom = b'
    rw [yonedaEquiv_symm_comp, ← Edge.map_edge, hmap]
    change yonedaEquiv.symm (yonedaEquiv b') = b'
    exact Equiv.symm_apply_apply _ _

/-- The supplied exact Cartesian marking lifts the original composition marking cell. -/
theorem compositionCell_cartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty compositionCell.{u} (cartesianProjection p) := by
  apply (compositionCell_rlp_iff (cartesianProjection p)).mpr
  intro t h₂ h₀
  let T : (Δ[2] : SSet.{u}) ⟶ E := t
  change CartesianEdge.IsPCartesian p (yonedaEquiv.symm
    (T.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))))) at h₂
  change CartesianEdge.IsPCartesian p (yonedaEquiv.symm
    (T.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))))) at h₀
  change CartesianEdge.IsPCartesian p (yonedaEquiv.symm
    (T.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3)))))
  rw [← yonedaEquiv_comp, Equiv.symm_apply_apply] at h₂ h₀ ⊢
  exact (CartesianEdge.isPCartesian_face_two_iff_face_one p T h₀).mp h₂

/-- The original dual triangle law lifts the composition cell against the supplied cocartesian marking. -/
theorem compositionCell_cocartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty compositionCell.{u} (cocartesianProjection p) := by
  apply (compositionCell_rlp_iff (cocartesianProjection p)).mpr
  intro t h₂ h₀
  let T : (Δ[2] : SSet.{u}) ⟶ E := t
  change CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm
    (T.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (2 : Fin 3))))) at h₂
  change CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm
    (T.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (0 : Fin 3))))) at h₀
  change CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm
    (T.app (op ⦋1⦌) (yonedaEquiv (stdSimplex.δ (1 : Fin 3)))))
  rw [← yonedaEquiv_comp, Equiv.symm_apply_apply] at h₂ h₀ ⊢
  exact (CocartesianEdge.isPCocartesian_face_zero_iff_face_one p T h₂).mp h₀

/-- All original inner cells lift against the exact intrinsic Cartesian projection. -/
theorem innerCell_cartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] (n : ℕ) (i : Fin (n + 3))
    (hi : 0 < i) (hi' : i < Fin.last (n + 2)) :
    HasLiftingProperty (innerCell.{u} n i) (cartesianProjection p) := by
  have hp : InnerFibration (cartesianProjection p).hom := by
    change InnerFibration p
    infer_instance
  exact (innerCell_rlp_iff (cartesianProjection p)).mpr hp n i hi hi'

/-- The original inner lifting specialization for cocartesian marking. -/
theorem innerCell_cocartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] (n : ℕ) (i : Fin (n + 3))
    (hi : 0 < i) (hi' : i < Fin.last (n + 2)) :
    HasLiftingProperty (innerCell.{u} n i) (cocartesianProjection p) := by
  have hp : InnerFibration (cocartesianProjection p).hom := by
    change InnerFibration p
    infer_instance
  exact (innerCell_rlp_iff (cocartesianProjection p)).mpr hp n i hi hi'

/-- Original critical final-horn lifting for the exact intrinsic Cartesian marking. -/
theorem cartesianCriticalCell_cartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] (n : ℕ) :
    HasLiftingProperty (cartesianCriticalCell.{u} n) (cartesianProjection p) :=
  (cartesianCriticalCell_rlp_iff (cartesianProjection p)).mpr (fun _ h => h) n

/-- Original critical initial-horn lifting for the exact intrinsic cocartesian marking. -/
theorem cocartesianCriticalCell_cocartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] (n : ℕ) :
    HasLiftingProperty (cocartesianCriticalCell.{u} n) (cocartesianProjection p) :=
  (cocartesianCriticalCell_rlp_iff (cocartesianProjection p)).mpr (fun _ h => h) n

/-- A genuine Cartesian fibration lifts the original target-endpoint cell in its canonical marking. -/
theorem cartesianEndpointCell_cartesian {E B : SSet.{u}} (p : E ⟶ B)
    [CartesianFibration p] [Quasicategory B] :
    HasLiftingProperty cartesianEndpointCell.{u} (cartesianProjection p) := by
  let _ : CartesianFibration (cartesianProjection p).hom := by
    change CartesianFibration p
    infer_instance
  exact cartesianEndpointCell_of_cartesianFibration (cartesianProjection p) (fun _ h => h)

/-- A genuine cocartesian fibration lifts the original source-endpoint cell in its canonical marking. -/
theorem cocartesianEndpointCell_cocartesian {E B : SSet.{u}} (p : E ⟶ B)
    [CocartesianFibration p] [Quasicategory B] :
    HasLiftingProperty cocartesianEndpointCell.{u} (cocartesianProjection p) := by
  let _ : CocartesianFibration (cocartesianProjection p).hom := by
    change CocartesianFibration p
    infer_instance
  exact cocartesianEndpointCell_of_cocartesianFibration (cocartesianProjection p) (fun _ h => h)

/-- The one fixed Kan equivalence-marking cell lifts against the intrinsic Cartesian projection. -/
theorem equivalenceMarkCell_cartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty equivalenceMarkCell.{u} (cartesianProjection p) := kanMarkCell_cartesian _ p

/-- The same fixed detector lifts against the original cocartesian projection. -/
theorem equivalenceMarkCell_cocartesian {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty equivalenceMarkCell.{u} (cocartesianProjection p) := kanMarkCell_cocartesian _ p

end SSet.Marked
