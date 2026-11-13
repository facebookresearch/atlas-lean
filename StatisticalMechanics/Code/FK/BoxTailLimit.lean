/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.FK.TwoPointInfinite
import Code.FK.CriticalPoint
import Code.IsingFK.FvES
import Code.IsingFK.MagPercoIdBox

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}













def boxBdryConnEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  boxRestrict d n ⁻¹'
    {ω' : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω' (IsingFK.boxOrigin d n)}





theorem boxBdryConnEvent_eq_iUnion (d n : ℕ) :
    boxBdryConnEvent d n
      = ⋃ v ∈ {v : boxVerts d n | boxBoundary d n v},
          boxConnEvent d n (IsingFK.boxOrigin d n) v := by
  ext ω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iUnion,
    boxConnEvent, ConnToBdry]
  constructor
  · rintro ⟨v, hv, hconn⟩
    exact ⟨v, hv, hconn⟩
  · rintro ⟨v, hv, hconn⟩
    exact ⟨v, hv, hconn⟩





theorem isClopen_boxBdryConnEvent (d n : ℕ) : IsClopen (boxBdryConnEvent d n) := by
  rw [boxBdryConnEvent_eq_iUnion]
  refine Set.Finite.isClopen_biUnion (Set.toFinite _) ?_
  exact fun v _ => isClopen_boxConnEvent d n (IsingFK.boxOrigin d n) v


theorem measurableSet_boxBdryConnEvent (d n : ℕ) :
    MeasurableSet (boxBdryConnEvent d n) :=
  (isClopen_boxBdryConnEvent d n).isOpen.measurableSet





theorem isIncreasing_boxBdryConnEvent (d n : ℕ) :
    IsIncreasing (boxBdryConnEvent d n) := by
  rw [boxBdryConnEvent_eq_iUnion]
  exact isUpperSet_iUnion₂ (fun v _ => isIncreasing_boxConnEvent d n (IsingFK.boxOrigin d n) v)








theorem extendEdge_preimage_boxBdryConnEvent (d n : ℕ) :
    extendEdge d n ⁻¹' (boxBdryConnEvent d n)
      = {ω : ConfigSpace (Sym2 (boxVerts d n)) |
          ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
  ext ω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq, boxRestrict_extendEdge]














theorem wiredFiniteMeasure_real_boxBdryConnEvent (d n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      = wiredConnToBdryProb (boxGraph d n) (boxBoundary d n) p (IsingFK.boxOrigin d n) := by
  classical
  have hA : MeasurableSet (boxBdryConnEvent d n) := measurableSet_boxBdryConnEvent d n
  
  have hw : (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
        (boxBdryConnEvent d n)
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num : (0:ℝ) < 2)).toMeasure
          (extendEdge d n ⁻¹' (boxBdryConnEvent d n))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, extendEdge_preimage_boxBdryConnEvent,
    wiredFkPMF_toMeasure_toReal d n hp hp1 (by norm_num : (0:ℝ) < 2)]
  
  rw [wiredConnToBdryProb_eq_wiredFkProb_sum (boxGraph d n) (boxBoundary d n) p
    (IsingFK.boxOrigin d n)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hω : ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)
  · rw [if_pos hω, if_pos hω, one_mul]
  · rw [if_neg hω, if_neg hω, zero_mul]












theorem boxBoundaryConnProfile_eq_wiredFiniteMeasure_real (d n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0:ℝ) < 2) n
      = (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  rw [IsingFK.boxBoundaryConnProfile, wiredFiniteMeasure_real_boxBdryConnEvent d n hp hp1]


























theorem boxBoundaryConnProfile_tendsto_of_diag (d : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdiag : Tendsto
      (fun n => (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2)))) :
    Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0:ℝ) < 2) n)
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) := by
  refine hdiag.congr (fun n => ?_)
  exact (boxBoundaryConnProfile_eq_wiredFiniteMeasure_real d n hp hp1).symm

end FK

end StatMech
