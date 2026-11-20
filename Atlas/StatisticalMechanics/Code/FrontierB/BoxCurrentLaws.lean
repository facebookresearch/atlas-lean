/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.FiniteBoundaryCurrentLaw
import Code.FrontierB.InfiniteCurrentCompactness
import Code.FK.InfiniteVolume

open MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Lattice


def boxCurrentEdgeIncl (d n : ℕ) :
    (StatMech.FK.boxGraph d n).edgeFinset → Sym2 (Site d) :=
  fun e => StatMech.FK.edgeIncl d n e.1


theorem boxCurrentEdgeIncl_injective (d n : ℕ) :
    Function.Injective (boxCurrentEdgeIncl d n) := by
  intro e f hef
  apply Subtype.ext
  exact StatMech.FK.edgeIncl_injective d n hef


noncomputable def extendBoxCurrent (d n : ℕ)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n)) :
    InfiniteCurrentConfig (Sym2 (Site d)) :=
  fun e => if h : e ∈ Set.range (boxCurrentEdgeIncl d n) then m h.choose else 0


@[simp] theorem extendBoxCurrent_included (d n : ℕ)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n))
    (e : (StatMech.FK.boxGraph d n).edgeFinset) :
    extendBoxCurrent d n m (boxCurrentEdgeIncl d n e) = m e := by
  unfold extendBoxCurrent
  split
  · rename_i h
    exact congrArg m (boxCurrentEdgeIncl_injective d n h.choose_spec)
  · rename_i h
    exact (h ⟨e, rfl⟩).elim


theorem extendBoxCurrent_outside (d n : ℕ)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n))
    (e : Sym2 (Site d)) (he : e ∉ Set.range (boxCurrentEdgeIncl d n)) :
    extendBoxCurrent d n m e = 0 := by
  simp [extendBoxCurrent, he]


theorem measurable_extendBoxCurrent (d n : ℕ) :
    Measurable (extendBoxCurrent d n) :=
  Measurable.of_discrete


noncomputable def freeBoxCurrentMeasure (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨((sourcelessCurrentPMF (StatMech.FK.boxGraph d n) beta
      (fun _ => 1) hbeta (fun _ => by positivity)).toMeasure).map
      (extendBoxCurrent d n),
    Measure.isProbabilityMeasure_map
      (measurable_extendBoxCurrent d n).aemeasurable⟩


noncomputable def boxCurrentInterior (d n : ℕ) :
    Finset (StatMech.FK.boxVerts d n) :=
  Finset.univ.filter (fun x => ¬ StatMech.FK.boxBoundary d n x)


noncomputable def plusBoxCurrentMeasure (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  ⟨((boundaryCurrentPMF (StatMech.FK.boxGraph d n) beta
      (fun _ => 1) hbeta (fun _ => by positivity)
      (boxCurrentInterior d n)).toMeasure).map
      (extendBoxCurrent d n),
    Measure.isProbabilityMeasure_map
      (measurable_extendBoxCurrent d n).aemeasurable⟩


theorem freeBoxCurrentMeasure_edge_tail (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) (e : (StatMech.FK.boxGraph d n).edgeFinset) (K : ℕ) :
    (freeBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} =
      (sourcelessCurrentMeasure (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity) :
          Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d n)
      ((sourcelessCurrentPMF (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity)).toMeasure)
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d n e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]


theorem plusBoxCurrentMeasure_edge_tail (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) (e : (StatMech.FK.boxGraph d n).edgeFinset) (K : ℕ) :
    (plusBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} =
      (boundaryCurrentMeasure (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n) :
          Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
  change Measure.map (extendBoxCurrent d n)
      ((boundaryCurrentPMF (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n)).toMeasure)
        {m | K ≤ m (boxCurrentEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K ≤ m (boxCurrentEdgeIncl d n e)} :=
    (measurable_pi_apply (boxCurrentEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
  congr 1
  ext m
  simp [extendBoxCurrent_included]

end StatMech.FrontierB
