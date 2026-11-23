/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolumeFKG
/-!
# Free and wired infinite-volume limits at `q = 2`

The free and wired box measures of an increasing cylinder event converge along the whole
sequence to the infinite-volume values, and the free value is at most the wired one (`q = 2`).

## i. Overview

This file packages `fk_free_infinite_measure`, `fk_wired_infinite_measure` and
`ivp_iv_monotone` into one statement, and into the subsequence form used by consumers that work
with weak subsequential limits.

## ii. Key results

- `mvl_infiniteVolume_extremal` : convergence of both sequences and `φ⁰(S) ≤ φ¹(S)`.
- `mvl_infiniteVolume_extremal_subseq` : the same, in subsequence form.

## iii. Table of contents

- A. Ordered infinite-volume limits

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}

/-!
## A. Ordered infinite-volume limits
-/

/-- At `q = 2`, for an increasing cylinder event `S`, `φ⁰_m(S) → φ⁰(S)`, `φ¹_m(S) → φ¹(S)`, and
`φ⁰(S) ≤ φ¹(S)`. -/
lemma mvl_infiniteVolume_extremal (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
    ∧ Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
        (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
    ∧ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
        ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) :=
  ⟨fk_free_infinite_measure N hp hp1 hS, fk_wired_infinite_measure N hp hp1 hS,
    ivp_iv_monotone N hp hp1 hS⟩

/-- Subsequence form of `mvl_infiniteVolume_extremal` (with the identity subsequence). -/
lemma mvl_infiniteVolume_extremal_subseq (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    ∃ (ψ : ℕ → ℕ)
      (φ0 φ1 : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))),
      StrictMono ψ
        ∧ φ0 = freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        ∧ φ1 = wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        ∧ Tendsto (fun m => (freeFiniteMeasure d (ψ m) hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
            (𝓝 ((φ0 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
        ∧ Tendsto (fun m => (wiredFiniteMeasure d (ψ m) hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
            (𝓝 ((φ1 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)))
        ∧ (φ0 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
            ≤ (φ1 : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  refine ⟨id, freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2),
    wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2), strictMono_id, rfl, rfl, ?_, ?_, ?_⟩
  · simpa using fk_free_infinite_measure N hp hp1 hS
  · simpa using fk_wired_infinite_measure N hp hp1 hS
  · exact ivp_iv_monotone N hp hp1 hS

end FK

end StatMech
