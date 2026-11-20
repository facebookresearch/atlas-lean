/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorFiniteGraph
import Code.Universality.RSWFailureComplementaryArcObstruction











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section


theorem rlc_scaleTwoDoubleFailure_origin_mem_leftPath :
    origin 2 ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1 := by
  rw [show origin 2 = (![0, 0] : Site 2) by
    ext i
    fin_cases i <;> rfl]
  rw [rlc_scaleTwoDoubleFailure_left_vertices]
  simp


theorem rlc_scaleTwoDoubleFailure_origin_not_connectorAllowed :
    origin 2 ∉ rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  intro ho
  have hnotBarrier := (Finset.mem_sdiff.mp ho).2
  apply hnotBarrier
  rw [show origin 2 = (![0, 0] : Site 2) by
    ext i
    fin_cases i <;> rfl]
  rw [rlc_axis_mem_connectorBarrier_iff]
  right
  rw [rlc_scaleTwoDoubleFailure_left_vertices]
  simp


theorem rlc_scaleTwoDoubleFailure_originRegion_eq_empty :
    rlc_connectorOriginRegion rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro z
  intro hz
  rw [rlc_connectorOriginRegion] at hz
  simp only [Set.Finite.mem_toFinset] at hz
  exact rlc_scaleTwoDoubleFailure_origin_not_connectorAllowed hz.2.1


theorem rlc_scaleTwoDoubleFailure_connectorEdges_eq_empty :
    rlc_connectorEdges rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e
  intro he
  rw [rlc_connectorEdges, Finset.mem_filter] at he
  obtain ⟨z, hz, _⟩ := he.2
  rw [rlc_scaleTwoDoubleFailure_originRegion_eq_empty] at hz
  simp at hz


theorem rlc_scaleTwoDoubleFailure_exposedPaths_disjoint :
    Disjoint (rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
      (rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hz
  rw [rlc_scaleTwoDoubleFailure_left_vertices] at hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all



theorem rlc_scaleTwoDoubleFailure_finiteConnector_failure
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 2))) :
    tau ∉ rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  intro hconn
  obtain ⟨x, y, hx, hy, hxy⟩ := hconn
  have hopen : FK.openSub
      (rlc_connectorFiniteGraph rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft) tau = ⊥ := by
    ext u v
    simp [FK.openSub_adj, rlc_connectorFiniteGraph,
      rlc_scaleTwoDoubleFailure_connectorEdges_eq_empty]
  rw [hopen] at hxy
  have hxyEq : x = y := SimpleGraph.reachable_bot.mp hxy
  subst y
  exact Finset.disjoint_left.mp
    rlc_scaleTwoDoubleFailure_exposedPaths_disjoint hx hy



theorem rlc_scaleTwoDoubleFailure_PIMS_failure
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 2))) :
    rlc_connectorPIMSReflectedConfig rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft tau ∉
      rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft :=
  rlc_scaleTwoDoubleFailure_finiteConnector_failure _



theorem rlc_scaleTwoDoubleFailure_not_actualSelectedArc
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 2))) :
    ¬ RlcConnectorPIMSActualSelectedArc rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft tau := by
  intro harc
  exact rlc_scaleTwoDoubleFailure_PIMS_failure tau
    (rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft tau harc)



theorem rlc_failure_not_imply_actualSelectedArc_scaleTwo :
    ¬ (∀ tau : ConfigSpace (Sym2 (RlcConnectorVertex 2)),
      tau ∉ rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight
          rlc_scaleTwoDoubleFailureLeft →
        RlcConnectorPIMSActualSelectedArc rlc_scaleTwoDoubleFailureRight
          rlc_scaleTwoDoubleFailureLeft tau) := by
  intro h
  let tau : ConfigSpace (Sym2 (RlcConnectorVertex 2)) := fun _ => false
  exact rlc_scaleTwoDoubleFailure_not_actualSelectedArc tau
    (h tau (rlc_scaleTwoDoubleFailure_finiteConnector_failure tau))

end

end StatMech.Universality
