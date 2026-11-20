/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStraightLineEmbedding
import Code.Onsager.StateWeightedDeletion








open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA



theorem kwStraightLineGraph_bothOrientation_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (weight : Sym2 V → ℂ) (selected : G.Dart) :
    (∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n)
        selected selected.symm,
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight embedding.turnPhase) loop) = 0 := by
  let transition := kwGraphTransition G weight embedding.turnPhase
  apply StatMech.Onsager.ons_sum_zero_of_sign_involution'
    transition
    (StatMech.Onsager.ons_loopSetBoth (n := n) selected selected.symm)
    (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm)
  · intro loop hloop
    apply (StatMech.Onsager.ons_mem_loopSetBoth selected selected.symm _).mpr
    exact StatMech.Onsager.ons_surgery_visitsBoth
      SimpleGraph.Dart.symm_involutive
      (SimpleGraph.Dart.symm_ne selected)
      ((StatMech.Onsager.ons_mem_loopSetBoth selected selected.symm loop).mp hloop)
  · intro loop hloop
    exact kwStraightLineGraphLoopWeight_turnPhase_surgery_sign
      G embedding weight selected loop
        ((StatMech.Onsager.ons_mem_loopSetBoth
          selected selected.symm loop).mp hloop)
  · intro loop hloop
    exact StatMech.Onsager.ons_surgery_involutive
      SimpleGraph.Dart.symm_involutive
      (SimpleGraph.Dart.symm_ne selected)
      ((StatMech.Onsager.ons_mem_loopSetBoth selected selected.symm loop).mp hloop)



theorem kwStraightLineGraph_oneOrientation_sum_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (weight : Sym2 V → ℂ) (selected : G.Dart) :
    (∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → G.Dart ↦
          (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm),
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight embedding.turnPhase) loop) =
      ∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → G.Dart ↦
          (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected),
        StatMech.Onsager.ons_loopWeight
          (kwGraphTransition G weight embedding.turnPhase) loop := by
  apply StatMech.Onsager.ons_matrixLoopSum_orientation_symm_of_loopRev
    SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive _ _ selected
  intro loop
  exact kwStraightLineGraphLoopWeight_loopRev G embedding weight loop



theorem kwStraightLineGraph_detWalkRoot_delete_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → ℂ) (selected : G.Dart)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G weight embedding.turnPhase) =
      StatMech.Onsager.ons_detWalkRoot
          (StatMech.Onsager.ons_maskMatrix
            ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight embedding.turnPhase)) *
        (1 - ∑' path, StatMech.Onsager.ons_firstReturnWeight
          (kwGraphTransition G weight embedding.turnPhase)
          selected selected.symm path) := by
  apply StatMech.Onsager.ons_detWalkRoot_matrix_delete_pair
    _ selected selected.symm (SimpleGraph.Dart.symm_ne selected).symm
      q hq hentry hsmall hcard
  · intro n
    exact kwStraightLineGraph_bothOrientation_sum_zero
      G embedding weight selected
  · intro n
    exact kwStraightLineGraph_oneOrientation_sum_symm
      G embedding weight selected



theorem kwStraightLineGraph_detWalkRoot_scaleColumns_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → ℂ) (selected : G.Dart) (t : ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖StatMech.Onsager.ons_scaleColumns
        ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight embedding.turnPhase) dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (StatMech.Onsager.ons_scaleColumns
          ({selected, selected.symm} : Finset G.Dart) t
          (kwGraphTransition G weight embedding.turnPhase)) =
      StatMech.Onsager.ons_detWalkRoot
          (StatMech.Onsager.ons_maskMatrix
            ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight embedding.turnPhase)) *
        (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight
          (kwGraphTransition G weight embedding.turnPhase)
          selected selected.symm path) := by
  let M := kwGraphTransition G weight embedding.turnPhase
  let scaledWeight := kwScaleGraphEdgeWeight weight selected.edge t
  let Ms := kwGraphTransition G scaledWeight embedding.turnPhase
  let Mt := StatMech.Onsager.ons_scaleColumns
    ({selected, selected.symm} : Finset G.Dart) t M
  have hboth : ∀ n : ℕ,
      (∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n + 1)
          selected selected.symm,
        StatMech.Onsager.ons_loopWeight Mt loop) = 0 := by
    intro n
    calc
      (∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n + 1)
          selected selected.symm,
        StatMech.Onsager.ons_loopWeight Mt loop) =
          ∑ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n + 1)
            selected selected.symm,
          StatMech.Onsager.ons_loopWeight Ms loop := by
            apply Finset.sum_congr rfl
            intro loop _
            exact (kw_loopWeight_scaleGraphEdge_eq_scaleColumns
              G weight embedding.turnPhase selected t loop).symm
      _ = 0 := kwStraightLineGraph_bothOrientation_sum_zero
        G embedding scaledWeight selected
  have hloopRev : ∀ {n : ℕ} [NeZero n] (loop : Fin n → G.Dart),
      StatMech.Onsager.ons_loopWeight Mt
          (StatMech.Onsager.ons_involutiveLoopRev
            SimpleGraph.Dart.symm loop) =
        StatMech.Onsager.ons_loopWeight Mt loop := by
    intro n hn loop
    rw [← kw_loopWeight_scaleGraphEdge_eq_scaleColumns
        G weight embedding.turnPhase selected t,
      ← kw_loopWeight_scaleGraphEdge_eq_scaleColumns
        G weight embedding.turnPhase selected t]
    exact kwStraightLineGraphLoopWeight_loopRev
      G embedding scaledWeight loop
  have hsymm : ∀ n : ℕ,
      (∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → G.Dart ↦
            (∃ i, loop i = selected) ∧ ¬∃ j, loop j = selected.symm),
        StatMech.Onsager.ons_loopWeight Mt loop) =
        ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → G.Dart ↦
            (∃ i, loop i = selected.symm) ∧ ¬∃ j, loop j = selected),
          StatMech.Onsager.ons_loopWeight Mt loop := by
    intro n
    apply StatMech.Onsager.ons_matrixLoopSum_orientation_symm_of_loopRev
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive Mt
        (fun loop ↦ hloopRev loop) selected
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
    · have hnext : ¬(next = selected ∨ next = selected.symm) := by tauto
      simp [hnext]
  have hfirst :
      (∑' path, StatMech.Onsager.ons_firstReturnWeight
          Mt selected selected.symm path) =
        t * ∑' path, StatMech.Onsager.ons_firstReturnWeight
          M selected selected.symm path := by
    exact StatMech.Onsager.ons_tsum_firstReturnWeight_scale
      M selected selected.symm t
  change StatMech.Onsager.ons_detWalkRoot Mt = _
  rw [hdelete, hmask, hfirst]


theorem kwStraightLineGraph_detWalkRoot_scaleEdge_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → ℂ) (selected : G.Dart) (t : ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖StatMech.Onsager.ons_scaleColumns
        ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight embedding.turnPhase) dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t)
          embedding.turnPhase) =
      StatMech.Onsager.ons_detWalkRoot
          (StatMech.Onsager.ons_maskMatrix
            ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight embedding.turnPhase)) *
        (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight
          (kwGraphTransition G weight embedding.turnPhase)
          selected selected.symm path) := by
  rw [kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns]
  exact kwStraightLineGraph_detWalkRoot_scaleColumns_affine
    G embedding weight selected t q hq hentry hsmall hcard

end StatMech.FrontierA
