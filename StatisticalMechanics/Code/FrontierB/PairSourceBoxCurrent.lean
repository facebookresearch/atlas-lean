/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.SourceCurrentTail
import Code.FrontierB.BoxGraphPath
import Code.FrontierB.BoxCurrentLaws
import Code.FrontierB.FiniteCurrentPairLaw

open MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Lattice


theorem boxCurrentSum_pair_pos
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    0 < currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} :=
  currentSum_pair_pos_of_path (StatMech.FK.boxGraph d n) beta
    (fun _ => 1) hbeta (fun _ => by positivity)
    (boxGraphPath d n x y) (boxGraphPath_isPath d n x y) hxy



noncomputable def pairSourceBoxCurrentMeasure
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨(currentPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
      (fun _ => by positivity) {x, y}
      (boxCurrentSum_pair_pos d n beta hbeta x y hxy)).toMeasure.map
      (extendBoxCurrent d n),
    Measure.isProbabilityMeasure_map
      (measurable_extendBoxCurrent d n).aemeasurable⟩



theorem pairSourceBoxCurrentMeasure_prod_apply
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d)))) (hC : MeasurableSet C) :
    ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _) C =
      (sourceCurrentPairPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1)
        hbeta.le (fun _ => by positivity) {x, y} {x, y}
        (boxCurrentSum_pair_pos d n beta hbeta x y hxy)
        (boxCurrentSum_pair_pos d n beta hbeta x y hxy)).toMeasure
          ((Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' C) := by
  let G := StatMech.FK.boxGraph d n
  let mu := (currentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) {x, y}
    (boxCurrentSum_pair_pos d n beta hbeta x y hxy)).toMeasure
  change (Measure.map (extendBoxCurrent d n) mu).prod
      (Measure.map (extendBoxCurrent d n) mu) C = _
  rw [Measure.map_prod_map mu mu (measurable_extendBoxCurrent d n)
    (measurable_extendBoxCurrent d n),
    Measure.map_apply
      ((measurable_extendBoxCurrent d n).prodMap
        (measurable_extendBoxCurrent d n)) hC,
    sourceCurrentPairPMF_toMeasure_eq_prod]


noncomputable def boxPairCorrelationConstant
    (d n : ℕ) (beta : ℝ)
    (x y : StatMech.FK.boxVerts d n) : ℝ :=
  pathCorrelationConstant (StatMech.FK.boxGraph d n) beta
    (fun _ => 1) Finset.univ (boxGraphPath d n x y)

theorem boxPairCorrelationConstant_pos
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) :
    0 < boxPairCorrelationConstant d n beta x y := by
  apply pathCorrelationConstant_pos (StatMech.FK.boxGraph d n) beta
    (fun _ => 1) Finset.univ (boxGraphPath d n x y) hbeta
  · intro e he
    positivity
  · intro z hz
    simp

theorem boxPairCorrelationConstant_le_expectation
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    boxPairCorrelationConstant d n beta x y ≤
      expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} := by
  exact pathCorrelationConstant_le_expectation
    (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) Finset.univ (boxGraphPath d n x y)
    (boxGraphPath_isPath d n x y) hxy



theorem pairSourceBoxCurrentMeasure_edge_tail
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (e : (StatMech.FK.boxGraph d n).edgeFinset) (K : ℕ) :
    (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} =
      (sourceCurrentMeasure (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta.le (fun _ => by positivity) {x, y}
        (boxCurrentSum_pair_pos d n beta hbeta x y hxy) :
          Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d n) _
      {m | K ≤ m (boxCurrentEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d n e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]



theorem pairSourceBoxCurrentMeasure_edge_inverse_tail_le
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (K : ℕ) (hK : 0 < K) :
    (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} ≤
      ENNReal.ofReal
        (Real.exp beta / (boxPairCorrelationConstant d n beta x y * K)) := by
  rw [pairSourceBoxCurrentMeasure_edge_tail]
  simpa using sourceCurrentMeasure_edge_inverse_tail_le
    (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) {x, y}
    (boxCurrentSum_pair_pos d n beta hbeta x y hxy) e
    (boxPairCorrelationConstant d n beta x y)
    (boxPairCorrelationConstant_pos d n beta hbeta x y)
    (boxPairCorrelationConstant_le_expectation d n beta hbeta x y hxy)
    K hK

end StatMech.FrontierB
