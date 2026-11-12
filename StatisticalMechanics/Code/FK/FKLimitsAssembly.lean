/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.FK.MonotoneWeakLimit
import Code.FK.FreeWeakLimit
import Code.FK.MonotoneVolumeLimit
import Code.FK.BulkDeviationProof
import Code.FK.FKLimitsClose
import Code.FK.FKErgodicClose
import Mathlib

open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}



















theorem fla_fk_limits (d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro N S hS
    exact fk_free_infinite_measure N hp hp1 hS
  · 
    intro N S hS
    exact fk_wired_infinite_measure N hp hp1 hS
  · 
    exact bdp_freeIV_isTranslationInvariant hp hp1
  · 
    exact flc_wiredIV_isTranslationInvariant hp hp1
  · 
    exact fec_freeIV_isErgodic_of_extremePoint hp hp1
      (bdp_freeIV_isTranslationInvariant hp hp1) hextF
  · 
    exact fec_wiredIV_isErgodic_of_extremePoint hp hp1 hextW
  · 
    intro N S hS
    exact (mvl_infiniteVolume_extremal N hp hp1 hS).2.2








example : True := by
  have h : ∀ (hextW : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site 2)))) (a b : ℝ≥0∞),
      IsTranslationInvariant (G := Multiplicative (Site 2)) ν₁ →
        IsTranslationInvariant (G := Multiplicative (Site 2)) ν₂ →
          IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
            0 < a → 0 < b → a + b = 1 →
              (wiredInfiniteVolume 2 (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1)
                  (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site 2)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂)
      (hextF : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site 2)))) (a b : ℝ≥0∞),
      IsTranslationInvariant (G := Multiplicative (Site 2)) ν₁ →
        IsTranslationInvariant (G := Multiplicative (Site 2)) ν₂ →
          IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
            0 < a → 0 < b → a + b = 1 →
              (freeInfiniteVolume 2 (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1)
                  (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site 2)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂), True := by
    intro hextW hextF
    have := fla_fk_limits 2 (by norm_num) (p := 1/2) (by norm_num) (by norm_num) hextW hextF
    trivial
  trivial







#print axioms fla_fk_limits

end FK

end StatMech
