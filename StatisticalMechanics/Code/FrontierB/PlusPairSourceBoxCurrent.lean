/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.FiniteBoundarySourceLaw
import Code.FrontierB.PairSourceBoxCurrent
import Code.IsingFK.HisingBoxClose

open MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Lattice
open StatMech.IsingFK


def boxSiteSucc {d n : ℕ} (x : StatMech.FK.boxVerts d n) :
    StatMech.FK.boxVerts d (n + 1) :=
  ⟨x.1, box_subset_succ d n x.2⟩

theorem boxSiteSucc_interior {d n : ℕ}
    (x : StatMech.FK.boxVerts d n) :
    boxSiteSucc x ∈ boxCurrentInterior d (n + 1) := by
  have hnot : ¬ StatMech.FK.boxBoundary d (n + 1) (boxSiteSucc x) := by
    rw [hbx_boxBoundary_succ_iff]
    exact not_not_intro x.2
  simp [boxCurrentInterior, hnot]

theorem boxSiteSucc_ne {d n : ℕ}
    {x y : StatMech.FK.boxVerts d n} (hxy : x ≠ y) :
    boxSiteSucc x ≠ boxSiteSucc y := by
  intro h
  apply hxy
  apply Subtype.ext
  exact congrArg (fun z => z.1) h

theorem pair_boxSiteSucc_inter_interior {d n : ℕ}
    (x y : StatMech.FK.boxVerts d n) :
    ({boxSiteSucc x, boxSiteSucc y} :
        Finset (StatMech.FK.boxVerts d (n + 1))) ∩
        boxCurrentInterior d (n + 1) =
      {boxSiteSucc x, boxSiteSucc y} := by
  apply Finset.inter_eq_left.mpr
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact boxSiteSucc_interior x
  · exact boxSiteSucc_interior y


theorem plusPairBoundarySourceCurrentSum_pos
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    0 < boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
      (fun _ => 1) (boxCurrentInterior d (n + 1))
      {boxSiteSucc x, boxSiteSucc y} := by
  apply boundarySourceCurrentSum_pos_of_currentSum_pos
    (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
    hbeta.le (fun _ => by positivity)
    (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y}
    {boxSiteSucc x, boxSiteSucc y}
  · exact pair_boxSiteSucc_inter_interior x y
  · exact boxCurrentSum_pair_pos d (n + 1) beta hbeta
      (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)



noncomputable def plusPairSourceBoxCurrentMeasure
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨((boundarySourceCurrentPMF (StatMech.FK.boxGraph d (n + 1)) beta
      (fun _ => 1) hbeta.le (fun _ => by positivity)
      (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y}
      (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy)).toMeasure).map
      (extendBoxCurrent d (n + 1)),
    Measure.isProbabilityMeasure_map
      (measurable_extendBoxCurrent d (n + 1)).aemeasurable⟩



theorem plusPairSourceBoxCurrentMeasure_edge_tail
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (e : (StatMech.FK.boxGraph d (n + 1)).edgeFinset) (K : ℕ) :
    (plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d (n + 1) e)} =
      (boundarySourceCurrentPMF (StatMech.FK.boxGraph d (n + 1)) beta
        (fun _ => 1) hbeta.le (fun _ => by positivity)
        (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y}
        (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy)).toMeasure
          {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d (n + 1)) _
      {m | K ≤ m (boxCurrentEdgeIncl d (n + 1) e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d (n + 1) e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d (n + 1) e))
      MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]

end StatMech.FrontierB
