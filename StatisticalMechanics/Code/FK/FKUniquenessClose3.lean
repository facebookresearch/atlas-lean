/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.FK.FKUniquenessClose
import Code.FK.FKUniquenessClose2
import Code.FK.FreeWeakLimit
import Code.FK.MonotoneWeakLimit
import Code.FK.Limits

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}
























theorem freeEdgeDensity_q2_le_wiredEdgeDensity (d N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p ≤ wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
  
  rw [freeEdgeDensity_q2_eq_real d N eb hp hp1, wiredEdgeDensity_q2_eq_real d N eb hp hp1]
  
  have htend_free :=
    fk_free_infinite_measure (d := d) N hp hp1 (boxEdgeOpenEvent_isIncreasing d N eb)
  
  have htend_wired := wiredEdgeDensity_q2_tendsto d N eb hp hp1
  rw [wiredEdgeDensity_q2_eq_real d N eb hp hp1] at htend_wired
  
  have hmono : ∀ m, (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := fun m =>
    freeFiniteMeasure_dominated d m hp hp1 (by norm_num)
      (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
      (fkWiredLimit_measurableSet_preimage N (boxEdgeOpenEvent d N eb))
      (isIncreasing_boxRestrict_boxEdgeOpenEvent d N eb)
  
  exact le_of_tendsto_of_tendsto htend_free htend_wired (Filter.Eventually.of_forall hmono)


















theorem density_le_of_secant_continuousWithinAt {b : ℝ → ℝ} {a p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hcont : ContinuousWithinAt b (Ioo (0:ℝ) 1) p)
    (hsec : ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → b p' ≤ a) :
    b p ≤ a := by
  
  have hsub : Ioo (0:ℝ) p ⊆ Ioo (0:ℝ) 1 := fun x hx => ⟨hx.1, hx.2.trans hp1⟩
  have hcont' : ContinuousWithinAt b (Ioo (0:ℝ) p) p := hcont.mono hsub
  have hne : (𝓝[Ioo (0:ℝ) p] p).NeBot := right_nhdsWithin_Ioo_neBot hp0
  have htend : Tendsto b (𝓝[Ioo (0:ℝ) p] p) (𝓝 (b p)) := hcont'
  
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hsec x (hsub hx) hx.2






























theorem heq_at_cont_q2_of_secant (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
    ∀ p ∈ Ioo (0 : ℝ) 1,
      ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p →
        freeEdgeDensity d 2 (edgeIncl d N eb) p
          = wiredEdgeDensity d 2 (edgeIncl d N eb) p := by
  intro p hpmem hcont
  obtain ⟨hp0, hp1⟩ := hpmem
  refine le_antisymm (freeEdgeDensity_q2_le_wiredEdgeDensity d N eb hp0 hp1) ?_
  
  exact density_le_of_secant_continuousWithinAt hp0 hp1 hcont
    (fun p' hp'mem hp'lt => hsecant p ⟨hp0, hp1⟩ p' hp'mem hp'lt)































theorem fk_uniqueness_off_countable_q2_full (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p →
      wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p) :
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
                  (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) :=
  fk_uniqueness_off_countable_q2_no_hb d N eb (heq_at_cont_q2_of_secant d N eb hsecant)

end FK

end StatMech
