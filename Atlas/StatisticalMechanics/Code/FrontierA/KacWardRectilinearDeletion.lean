/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierA.KacWardRectilinearGraphCancellation
import Code.Onsager.StateWeightedDeletion

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA



theorem kw_rectilinearGraph_loopRev_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (loop : Fin n -> G.Dart) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart)))
        (StatMech.Onsager.ons_involutiveLoopRev
          SimpleGraph.Dart.symm loop) =
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) loop := by
  rw [kwGraphTransition_turnW_eq_stateWeighted]
  exact StatMech.Onsager.ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev
    SimpleGraph.Dart.symm direction hdirection omega homega homega_sq
    (fun dart => weight dart.edge) (fun _ => 1)
    (by intro dart; simp)
    (kwGraphNonbacktrackingFactor G)
    (kwGraphNonbacktrackingFactor_reverse G) loop



theorem kw_rectilinearGraph_bothOrientation_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I) (selected : G.Dart) :
    (∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n)
        selected selected.symm,
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) loop) = 0 := by
  rw [kwGraphTransition_turnW_eq_stateWeighted]
  exact StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix_lemma5
    SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
    direction hdirection omega homega homega_sq
    (fun dart => weight dart.edge) (fun _ => 1)
    (by intro dart; simp)
    (kwGraphNonbacktrackingFactor G)
    (kwGraphNonbacktrackingFactor_reverse G)
    selected (SimpleGraph.Dart.symm_ne selected)


theorem kw_rectilinearGraph_oneOrientation_sum_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I) (selected : G.Dart) :
    (∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n -> G.Dart =>
          (∃ i, loop i = selected) ∧ ¬ ∃ j, loop j = selected.symm),
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) loop) =
      ∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n -> G.Dart =>
          (∃ i, loop i = selected.symm) ∧ ¬ ∃ j, loop j = selected),
        StatMech.Onsager.ons_loopWeight
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart))) loop := by
  apply StatMech.Onsager.ons_matrixLoopSum_orientation_symm_of_loopRev
    SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive _ _ selected
  intro loop
  exact kw_rectilinearGraph_loopRev_weight G weight direction hdirection
    omega homega homega_sq loop




theorem kw_rectilinearGraph_detWalkRoot_delete_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (selected : G.Dart) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight
        (fun d e => StatMech.Onsager.ons_turnW omega
          (direction e) (direction d)) dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G weight
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) =
      StatMech.Onsager.ons_detWalkRoot
          (StatMech.Onsager.ons_maskMatrix
            ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight
              (fun dart next => StatMech.Onsager.ons_turnW omega
                (direction next) (direction dart)))) *
        (1 - ∑' path, StatMech.Onsager.ons_firstReturnWeight
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart)))
          selected selected.symm path) := by
  apply StatMech.Onsager.ons_detWalkRoot_matrix_delete_pair
    _ selected selected.symm (SimpleGraph.Dart.symm_ne selected).symm
      q hq hentry hsmall hcard
  · intro n
    exact kw_rectilinearGraph_bothOrientation_sum_zero
      G weight direction hdirection omega homega homega_sq selected
  · intro n
    exact kw_rectilinearGraph_oneOrientation_sum_symm
      G weight direction hdirection omega homega homega_sq selected



theorem kw_dart_mem_reversePair_iff_edge_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (selected dart : G.Dart) :
    dart ∈ ({selected, selected.symm} : Finset G.Dart) ↔
      dart.edge = selected.edge := by
  rw [Finset.mem_insert, Finset.mem_singleton,
    SimpleGraph.dart_edge_eq_iff]



theorem kw_scaleColumns_graphTransition_eq_stateWeighted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (omega t : ℂ) (selected : G.Dart) :
    StatMech.Onsager.ons_scaleColumns
        ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) =
      StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix
        direction omega (fun dart => weight dart.edge)
        (fun dart => if dart.edge = selected.edge then t else 1)
        (kwGraphNonbacktrackingFactor G) := by
  rw [kwGraphTransition_turnW_eq_stateWeighted]
  ext dart next
  simp only [StatMech.Onsager.ons_scaleColumns,
    StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix]
  by_cases hmem : next ∈
    ({selected, selected.symm} : Finset G.Dart)
  · have hedge : next.edge = selected.edge :=
      (kw_dart_mem_reversePair_iff_edge_eq selected next).mp hmem
    simp [hmem, hedge]
    ring
  · have hedge : next.edge ≠ selected.edge := fun hedge =>
      hmem ((kw_dart_mem_reversePair_iff_edge_eq selected next).mpr hedge)
    simp [hmem, hedge]




theorem kw_rectilinearGraph_detWalkRoot_scaleColumns_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (selected : G.Dart) (t : ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖StatMech.Onsager.ons_scaleColumns
        ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight
          (fun d e => StatMech.Onsager.ons_turnW omega
            (direction e) (direction d))) dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (StatMech.Onsager.ons_scaleColumns
          ({selected, selected.symm} : Finset G.Dart) t
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart)))) =
      StatMech.Onsager.ons_detWalkRoot
          (StatMech.Onsager.ons_maskMatrix
            ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight
              (fun dart next => StatMech.Onsager.ons_turnW omega
                (direction next) (direction dart)))) *
        (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart)))
          selected selected.symm path) := by
  let M := kwGraphTransition G weight
    (fun dart next => StatMech.Onsager.ons_turnW omega
      (direction next) (direction dart))
  let Mt := StatMech.Onsager.ons_scaleColumns
    ({selected, selected.symm} : Finset G.Dart) t M
  have hstate : Mt =
      StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix
        direction omega (fun dart => weight dart.edge)
        (fun dart => if dart.edge = selected.edge then t else 1)
        (kwGraphNonbacktrackingFactor G) := by
    exact kw_scaleColumns_graphTransition_eq_stateWeighted
      G weight direction omega t selected
  have hweight : ∀ dart : G.Dart,
      weight dart.symm.edge *
          (if dart.symm.edge = selected.edge then t else 1) =
        weight dart.edge *
          (if dart.edge = selected.edge then t else 1) := by
    intro dart
    simp
  have hboth : ∀ n : ℕ,
      (∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n + 1)
          selected selected.symm,
        StatMech.Onsager.ons_loopWeight Mt loop) = 0 := by
    intro n
    rw [hstate]
    exact StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix_lemma5
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
      direction hdirection omega homega homega_sq
      (fun dart => weight dart.edge)
      (fun dart => if dart.edge = selected.edge then t else 1)
      hweight (kwGraphNonbacktrackingFactor G)
      (kwGraphNonbacktrackingFactor_reverse G)
      selected (SimpleGraph.Dart.symm_ne selected)
  have hloopRev : ∀ {n : ℕ} [NeZero n] (loop : Fin n -> G.Dart),
      StatMech.Onsager.ons_loopWeight Mt
          (StatMech.Onsager.ons_involutiveLoopRev
            SimpleGraph.Dart.symm loop) =
        StatMech.Onsager.ons_loopWeight Mt loop := by
    intro n hn loop
    rw [hstate]
    exact StatMech.Onsager.ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev
      SimpleGraph.Dart.symm direction hdirection omega homega homega_sq
      (fun dart => weight dart.edge)
      (fun dart => if dart.edge = selected.edge then t else 1)
      hweight (kwGraphNonbacktrackingFactor G)
      (kwGraphNonbacktrackingFactor_reverse G) loop
  have hsymm : ∀ n : ℕ,
      (∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) -> G.Dart =>
            (∃ i, loop i = selected) ∧ ¬ ∃ j, loop j = selected.symm),
        StatMech.Onsager.ons_loopWeight Mt loop) =
        ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) -> G.Dart =>
            (∃ i, loop i = selected.symm) ∧ ¬ ∃ j, loop j = selected),
          StatMech.Onsager.ons_loopWeight Mt loop := by
    intro n
    apply StatMech.Onsager.ons_matrixLoopSum_orientation_symm_of_loopRev
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive Mt
        (fun loop => hloopRev loop) selected
  have hdelete := StatMech.Onsager.ons_detWalkRoot_matrix_delete_pair
    Mt selected selected.symm (SimpleGraph.Dart.symm_ne selected).symm
      q hq hentry hsmall hcard hboth hsymm
  have hmask :
      StatMech.Onsager.ons_maskMatrix
          ({selected, selected.symm} : Finset G.Dart) Mt =
        StatMech.Onsager.ons_maskMatrix
          ({selected, selected.symm} : Finset G.Dart) M := by
    ext dart next
    simp only [Mt, StatMech.Onsager.ons_maskMatrix,
      StatMech.Onsager.ons_scaleColumns, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hforbidden :
        (dart = selected ∨ dart = selected.symm) ∨
          next = selected ∨ next = selected.symm
    · simp [hforbidden]
    · have hnext : ¬(next = selected ∨ next = selected.symm) := by
        tauto
      simp [hforbidden, hnext]
  have hfirst :
      (∑' path, StatMech.Onsager.ons_firstReturnWeight
          Mt selected selected.symm path) =
        t * ∑' path, StatMech.Onsager.ons_firstReturnWeight
          M selected selected.symm path := by
    exact StatMech.Onsager.ons_tsum_firstReturnWeight_scale
      M selected selected.symm t
  change StatMech.Onsager.ons_detWalkRoot Mt = _
  rw [hdelete, hmask, hfirst]


noncomputable def kwScaleGraphEdgeWeight
    {V : Type*} [DecidableEq V]
    (weight : Sym2 V -> ℂ) (edge : Sym2 V) (t : ℂ) :
    Sym2 V -> ℂ :=
  fun other => if other = edge then t * weight other else weight other



theorem kwGraphTransition_scaleEdge_entry
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ)
    (selected dart next : G.Dart) (t : ℂ) :
    kwGraphTransition G
        (kwScaleGraphEdgeWeight weight selected.edge t) phase dart next =
      (if dart.edge = selected.edge then t else 1) *
        kwGraphTransition G weight phase dart next := by
  classical
  unfold kwGraphTransition kwScaleGraphEdgeWeight
  by_cases hedge : dart.edge = selected.edge
  · simp [hedge]
    split <;> ring
  · simp [hedge]



theorem kw_loopWeight_scaleGraphEdge_eq_scaleColumns
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ)
    (selected : G.Dart) (t : ℂ) (loop : Fin n -> G.Dart) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t) phase) loop =
      StatMech.Onsager.ons_loopWeight
        (StatMech.Onsager.ons_scaleColumns
          ({selected, selected.symm} : Finset G.Dart) t
          (kwGraphTransition G weight phase)) loop := by
  unfold StatMech.Onsager.ons_loopWeight
  rw [Finset.prod_congr rfl (fun k _ =>
    kwGraphTransition_scaleEdge_entry
      G weight phase selected (loop k) (loop (k + 1)) t),
    Finset.prod_mul_distrib]
  have hreindex :
      (∏ k, if (loop (k + 1)).edge = selected.edge then t else 1) =
        ∏ k, if (loop k).edge = selected.edge then t else 1 :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k => if (loop k).edge = selected.edge then t else 1)
  rw [← hreindex, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [StatMech.Onsager.ons_scaleColumns]
  by_cases hmem : loop (k + 1) ∈
      ({selected, selected.symm} : Finset G.Dart)
  · have hedge : (loop (k + 1)).edge = selected.edge :=
      (kw_dart_mem_reversePair_iff_edge_eq selected _).mp hmem
    simp [hmem, hedge]
  · have hedge : (loop (k + 1)).edge ≠ selected.edge := fun hedge =>
      hmem ((kw_dart_mem_reversePair_iff_edge_eq selected _).mpr hedge)
    simp [hmem, hedge]



theorem kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ)
    (selected : G.Dart) (t : ℂ) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t) phase) =
      StatMech.Onsager.ons_detWalkRoot
        (StatMech.Onsager.ons_scaleColumns
          ({selected, selected.symm} : Finset G.Dart) t
          (kwGraphTransition G weight phase)) := by
  apply StatMech.Onsager.ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  exact kw_loopWeight_scaleGraphEdge_eq_scaleColumns
    G weight phase selected t loop


theorem kw_rectilinearGraph_detWalkRoot_scaleEdge_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (selected : G.Dart) (t : ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖StatMech.Onsager.ons_scaleColumns
        ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight
          (fun d e => StatMech.Onsager.ons_turnW omega
            (direction e) (direction d))) dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t)
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) =
      StatMech.Onsager.ons_detWalkRoot
          (StatMech.Onsager.ons_maskMatrix
            ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight
              (fun dart next => StatMech.Onsager.ons_turnW omega
                (direction next) (direction dart)))) *
        (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart)))
          selected selected.symm path) := by
  rw [kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns]
  exact kw_rectilinearGraph_detWalkRoot_scaleColumns_affine
    G weight direction hdirection omega homega homega_sq
    selected t q hq hentry hsmall hcard

end StatMech.FrontierA
