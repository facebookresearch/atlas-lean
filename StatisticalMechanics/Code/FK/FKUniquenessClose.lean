/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.FK.FKUniquenessFull
import Code.FK.MonotoneWeakLimit
import Code.FK.TwoPointInfinite

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice












def boxEdgeOpenEvent (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    Set (ConfigSpace (Sym2 (boxVerts d N))) :=
  {σ | σ eb = true}



theorem boxEdgeOpenEvent_isIncreasing (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    IsIncreasing (boxEdgeOpenEvent d N eb) := by
  intro x y hxy hx
  simp only [boxEdgeOpenEvent, mem_setOf_eq] at hx ⊢
  have hle := hxy eb
  rw [hx] at hle
  exact le_antisymm (by simp) hle







theorem fkEdgeOpenEvent_edgeIncl_eq_boxRestrict (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    fkEdgeOpenEvent (edgeIncl d N eb) = boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb) := by
  ext ω
  simp only [fkEdgeOpenEvent, boxEdgeOpenEvent, mem_setOf_eq, mem_preimage, boxRestrict]










theorem wiredEdgeDensity_q2_eq_real (d N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
  unfold wiredEdgeDensity
  rw [dif_pos ⟨hp, hp1, by norm_num⟩, fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]



theorem freeEdgeDensity_q2_eq_real (d N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
  unfold freeEdgeDensity
  rw [dif_pos ⟨hp, hp1, by norm_num⟩, fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]














theorem wiredEdgeDensity_q2_eq_fkWiredLimitValue (d N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = fkWiredLimitValue N hp hp1 (boxEdgeOpenEvent d N eb) := by
  rw [wiredEdgeDensity_q2_eq_real d N eb hp hp1]
  exact fkWiredLimit_wiredInfiniteVolume_eq N hp hp1 (boxEdgeOpenEvent_isIncreasing d N eb)





theorem wiredEdgeDensity_q2_tendsto (d N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
  rw [wiredEdgeDensity_q2_eq_real d N eb hp hp1]
  exact fk_wired_infinite_measure N hp hp1 (boxEdgeOpenEvent_isIncreasing d N eb)














theorem isIncreasing_boxRestrict_boxEdgeOpenEvent (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    IsIncreasing (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
  rw [← fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]
  exact isIncreasing_fkEdgeOpenEvent (edgeIncl d N eb)







theorem hcrit_edgeOpenEvent_q2 (d N : ℕ) (eb : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hdens : freeEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
  rw [← freeEdgeDensity_q2_eq_real d N eb hp hp1, ← wiredEdgeDensity_q2_eq_real d N eb hp hp1]
  exact hdens






































theorem fk_uniqueness_off_countable_q2 (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hb : Monotone (wiredEdgeDensity d 2 (edgeIncl d N eb)))
    (heq_at_cont : ∀ p, ContinuousAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) p →
      freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1)
        (phi : Measure (ConfigSpace (Sym2 (Site d)))),
        ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real
              (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) →
        phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
            = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
          ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
              = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
  
  refine ⟨{p : ℝ | freeEdgeDensity d 2 (edgeIncl d N eb) p
      ≠ wiredEdgeDensity d 2 (edgeIncl d N eb) p},
    countable_density_ne hb heq_at_cont, ?_⟩
  intro p hp hp0 hp1 phi hsand
  
  simp only [mem_setOf_eq, not_not] at hp
  
  have hfw := hcrit_edgeOpenEvent_q2 d N eb hp0 hp1 hp
  
  exact dlr_sandwich_unique hsand hfw

end FK

end StatMech
