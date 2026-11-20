/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.FK.FKLimitsAssembly
import Code.FK.CrossBoxGeneralKeystone
import Code.FK.DLRUniqueness
import Mathlib

open MeasureTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}






theorem feu_wiredIV_isErgodic (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cbk_wiredIV_isErgodic hd hp hp1




















theorem feu_wiredIV_extreme_on_invariants (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (ha : 0 < a) (hb : 0 < b)
    (hconv : (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂)
    {s : Set (ConfigSpace (Sym2 (Site d)))} (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site d),
      (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' s = s) :
    ν₁ s = ν₂ s :=
  ergodic_summands_eq_on_invariants (feu_wiredIV_isErgodic hd hp hp1) hconv ha hb hs hinv


















theorem feu_fk_limits_wired_unconditional (d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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
  · intro N S hS
    exact fk_free_infinite_measure N hp hp1 hS
  · intro N S hS
    exact fk_wired_infinite_measure N hp hp1 hS
  · exact bdp_freeIV_isTranslationInvariant hp hp1
  · exact flc_wiredIV_isTranslationInvariant hp hp1
  · exact fec_freeIV_isErgodic_of_extremePoint hp hp1
      (bdp_freeIV_isTranslationInvariant hp hp1) hextF
  · 
    exact feu_wiredIV_isErgodic hd hp hp1
  · intro N S hS
    exact (mvl_infiniteVolume_extremal N hp hp1 hS).2.2


























theorem feu_fk_limits_of_freeErg (d : ℕ) (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hFreeErg : IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    
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
  · intro N S hS
    exact fk_free_infinite_measure N hp hp1 hS
  · intro N S hS
    exact fk_wired_infinite_measure N hp hp1 hS
  · exact bdp_freeIV_isTranslationInvariant hp hp1
  · exact flc_wiredIV_isTranslationInvariant hp hp1
  · exact hFreeErg
  · exact feu_wiredIV_isErgodic hd hp hp1
  · intro N S hS
    exact (mvl_infiniteVolume_extremal N hp hp1 hS).2.2



#print axioms feu_wiredIV_isErgodic
#print axioms feu_wiredIV_extreme_on_invariants
#print axioms feu_fk_limits_wired_unconditional
#print axioms feu_fk_limits_of_freeErg

end FK

end StatMech
