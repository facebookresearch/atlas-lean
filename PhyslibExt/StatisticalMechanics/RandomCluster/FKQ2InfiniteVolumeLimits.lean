/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneWeakLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeWeakLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.MonotoneVolumeLimit
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.ExtremeIsErgodic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Infinite-volume limits of the `q = 2` random-cluster model

For `q = 2` the free and wired finite-volume random-cluster measures converge, the limits are
translation invariant, ergodic given extremality, and ordered on increasing events.

## i. Overview

This file collects, for the FK representation of the Ising model (`q = 2`) on `ℤ^d`, the convergence
of the free and wired box measures on increasing box events, the translation invariance of both
limits, their ergodicity, and the domination of the free limit by the wired limit.
`fk_q2_infiniteVolume_limits` is conditional: it takes `hextW` and `hextF`, which say that the wired
(resp. free) infinite-volume measure admits no nontrivial convex decomposition into
translation-invariant probability measures (extremality). These inputs are used only for the two
ergodicity conclusions; the convergence, translation-invariance and domination parts need only
`0 < p < 1`.

## ii. Key results

- `fk_q2_infiniteVolume_limits` : convergence, translation invariance, ergodicity (given `hextW`,
  `hextF`) and ordering of the free and wired `q = 2` limits.

## iii. Table of contents

- A. The assembled statement

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}

/-! ## A. The assembled statement -/

/-- For `q = 2`: the free and wired box measures converge on increasing box events, both limits
are translation invariant, they are ergodic provided they are extremal among
translation-invariant measures (`hextW`, `hextF`), and the free limit is dominated by the
wired one. -/
theorem fk_q2_infiniteVolume_limits (d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hextW : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞),
      IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ →
        IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ →
          IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
            0 < a → 0 < b → a + b = 1 →
              (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂)
    (hextF : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞),
      IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ →
        IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ →
          IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
            0 < a → 0 < b → a + b = 1 →
              (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂) :
    (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S →
        Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
          (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))))
    ∧ (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S →
        Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
          (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))))
    ∧ IsTranslationInvariant (G := Multiplicative (Site d))
        (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d))))
    ∧ IsTranslationInvariant (G := Multiplicative (Site d))
        (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d))))
    ∧ IsErgodic (G := Multiplicative (Site d))
        (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d))))
    ∧ IsErgodic (G := Multiplicative (Site d))
        (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d))))
    ∧ (∀ (N : ℕ) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing S →
        (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
          ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
  have _hd1 : 1 ≤ d := hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N S hS
    exact fk_free_infinite_measure N hp hp1 hS
  · intro N S hS
    exact fk_wired_infinite_measure N hp hp1 hS
  · exact bdp_freeIV_isTranslationInvariant hp hp1
  · exact flc_wiredIV_isTranslationInvariant hp hp1
  · exact fec_freeIV_isErgodic_of_extremePoint hp hp1
      (bdp_freeIV_isTranslationInvariant hp hp1) hextF
  · exact fec_wiredIV_isErgodic_of_extremePoint hp hp1 hextW
  · intro N S hS
    exact (mvl_infiniteVolume_extremal N hp hp1 hS).2.2

end FK

end StatMech
