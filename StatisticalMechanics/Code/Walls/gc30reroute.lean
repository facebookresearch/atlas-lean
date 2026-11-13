/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































































import Mathlib
import Code.Walls.gc29hdom
import Code.Ising.BackboneResummation
import Code.Ising.BackboneExists
import Code.Ising.HdomMultiplicity

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



















theorem gc30_reroute_false_at_general :
    ¬ gc29_BackboneReroute hmu_TriG 1 (fun _ => 1) {hmu_triM} ∅ 0 1 2 := by
  intro h
  exact hmu_hdom_refutable (gc29_hdom_of_backboneReroute hmu_TriG 1 (fun _ => 1) {hmu_triM} ∅ h)




















theorem gc30_backbone_for_allConn (m : Sharpness.Current V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hall : hnw_allConn G m o x y) :
    ∃ P ⊆ oddEdges G.edgeFinset m, srcP P = ({x, y} : Finset V)
      ∧ (∀ e ∈ P, Odd (m e))
      ∧ Disjoint (oddEdges G.edgeFinset (hmu_addBackbone P m)) P := by
  obtain ⟨_hxy', hoy', hox'⟩ := hall
  obtain ⟨P, hPsub, hPsrc, hPodd⟩ := bbe_backbone_exists G.edgeFinset m hox hoy hxy hox' hoy'
  exact ⟨P, hPsub, hPsrc, hPodd, hmu_addBackbone_oddEdges_disjoint G m P hPodd⟩










theorem gc30_addBackbone_sources (m : Sharpness.Current V) (P : Finset (Sym2 V))
    (hP : P ⊆ G.edgeFinset) (hPsrc : srcP P = ({x, y} : Finset V)) :
    Sharpness.sources G (hmu_addBackbone P m) = Sharpness.sources G m ∆ ({x, y} : Finset V) := by
  have := hnw_addBackbone_sources G m P hP
  rwa [hPsrc] at this






theorem gc30_addBackbone_injective (P : Finset (Sym2 V)) :
    Function.Injective (hmu_addBackbone (V := V) P) :=
  hmu_addBackbone_injective P















theorem gc30_surgery_posDisconnect_obstruction (m : Sharpness.Current V) (P : Finset (Sym2 V))
    {u v : V} (h : connP (posEdges G.edgeFinset m) u v) :
    connP (posEdges G.edgeFinset (hmu_addBackbone P m)) u v :=
  hmu_addBackbone_connPos_preserved G m P h








theorem gc30_surgery_not_noneConn (m : Sharpness.Current V) (P : Finset (Sym2 V)) {o x y : V}
    (hall : hnw_allConn G m o x y) :
    ¬ hnw_noneConn G (hmu_addBackbone P m) o x y := by
  obtain ⟨hxy', _, _⟩ := hall
  intro hnone
  exact hnone.1 (gc30_surgery_posDisconnect_obstruction G m P
    (connOdd_imp_connPos G.edgeFinset m hxy'))




















theorem gc30_reroute_of_backboneSurgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (hsurg : bbr_BackboneSurgery G β J M B o x y) :
    gc29_BackboneReroute G β J M B o x y :=
  gc29_backboneReroute_of_hdom G β J hβ hJ M B
    (bbr_hdom_of_surgery G β J hβ hJ M B o x y hsurg)






theorem gc30_native_gap_nonneg_of_backboneSurgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hsurg : bbr_BackboneSurgery G β J M B o x y) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y :=
  gc29_native_gap_nonneg_of_backboneReroute G β J M hnd B hm hox hoy hxy hcoh
    (gc30_reroute_of_backboneSurgery G β J hβ hJ M B o x y hsurg)











theorem gc30_backboneSurgery_of_allConn_free (β : ℝ) (J : Sym2 V → ℝ)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (hno : bbr_allFilter G M o x y = ∅) :
    bbr_BackboneSurgery G β J M B o x y :=
  bbr_surgery_satisfiable G β J M B o x y hno







theorem gc30_reroute_of_allConn_free (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (hno : bbr_allFilter G M o x y = ∅) :
    gc29_BackboneReroute G β J M B o x y :=
  gc30_reroute_of_backboneSurgery G β J hβ hJ M B o x y
    (gc30_backboneSurgery_of_allConn_free G β J M B o x y hno)

end StatMech.Walls
