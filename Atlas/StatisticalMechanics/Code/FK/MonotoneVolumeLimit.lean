/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.FK.IvPropertiesFull
import Code.FK.FreeWeakLimit
import Code.FK.MonotoneWeakLimit
import Code.FK.Limits
import Code.FK.InfiniteVolume

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}



















theorem mvl_free_tendsto (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) :=
  fk_free_infinite_measure N hp hp1 hS




theorem mvl_wired_tendsto (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) :=
  fk_wired_infinite_measure N hp hp1 hS























theorem mvl_infiniteVolume_extremal (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
    ∧ Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
        (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
    ∧ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
        ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) :=
  ⟨mvl_free_tendsto N hp hp1 hS, mvl_wired_tendsto N hp hp1 hS, ivp_iv_monotone N hp hp1 hS⟩


















theorem mvl_infiniteVolume_extremal_subseq (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    ∃ (ψ : ℕ → ℕ)
      (φ0 φ1 : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))),
      StrictMono ψ
        ∧ φ0 = freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        ∧ φ1 = wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        ∧ Tendsto (fun m => (freeFiniteMeasure d (ψ m) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
            (𝓝 ((φ0 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
        ∧ Tendsto (fun m => (wiredFiniteMeasure d (ψ m) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
            (𝓝 ((φ1 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
        ∧ (φ0 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
            ≤ (φ1 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  refine ⟨id, freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2),
    wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2), strictMono_id, rfl, rfl, ?_, ?_, ?_⟩
  · simpa using mvl_free_tendsto N hp hp1 hS
  · simpa using mvl_wired_tendsto N hp hp1 hS
  · exact ivp_iv_monotone N hp hp1 hS

end FK

end StatMech
