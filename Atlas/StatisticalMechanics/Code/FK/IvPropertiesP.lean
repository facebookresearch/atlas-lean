/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Mathlib
import Code.FK.IvPropertiesFull
import Code.FK.FKUniquenessClose2

open MeasureTheory Filter Topology SimpleGraph
open StatMech.Lattice StatMech.IsingFK
open scoped BigOperators

namespace StatMech.FK

variable {d : ℕ}



theorem freeFiniteMeasure_real_monotone_in_p (m : ℕ) {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hle : p₁ ≤ p₂) {T : Set (ConfigSpace (Sym2 (boxVerts d m)))}
    (hT : IsIncreasing T) (hmeas : MeasurableSet (boxRestrict d m ⁻¹' T)) :
    (freeFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T)
      ≤ (freeFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' T) := by
  rw [freeFiniteMeasure_real_boxRestrictEvent m hp₁ hp₁' (by norm_num) T hmeas,
    freeFiniteMeasure_real_boxRestrictEvent m hp₂ hp₂' (by norm_num) T hmeas]
  simpa only [bcProb_bot_eq_fkProb] using
    (bcProb_monotone_in_p (boxGraph d m) (⊥ : SimpleGraph (boxVerts d m))
      hp₁ hp₁' hp₂ hp₂' hle (by norm_num : (1 : ℝ) ≤ 2) hT)



theorem freeFiniteMeasure_real_monotone_in_p_inner (N m : ℕ) (hNm : N ≤ m)
    {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂)
    (hp₂' : p₂ < 1) (hle : p₁ ≤ p₂)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (freeFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S
  have hT : IsIncreasing T :=
    fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω
    simp only [T, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq]
  exact freeFiniteMeasure_real_monotone_in_p m hp₁ hp₁' hp₂ hp₂' hle hT hmeas



theorem ivp_free_iv_monotone_in_p (N : ℕ) {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hle : p₁ ≤ p₂) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS : IsIncreasing S) :
    (freeInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (freeInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  have hlim₁ := fk_free_infinite_measure N hp₁ hp₁' hS
  have hlim₂ := fk_free_infinite_measure N hp₂ hp₂' hS
  have hmono : ∀ᶠ m in atTop,
      (freeFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
        ≤ (freeFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
    filter_upwards [eventually_ge_atTop N] with m hNm
    exact freeFiniteMeasure_real_monotone_in_p_inner N m hNm hp₁ hp₁' hp₂ hp₂' hle hS
  exact le_of_tendsto_of_tendsto hlim₁ hlim₂ hmono



theorem ivp_wired_iv_monotone_in_p (N : ℕ) {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂) (hp₂' : p₂ < 1)
    (hle : p₁ ≤ p₂) {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hS : IsIncreasing S) :
    (wiredInfiniteVolume d hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredInfiniteVolume d hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  have hlim₁ := fk_wired_infinite_measure N hp₁ hp₁' hS
  have hlim₂ := fk_wired_infinite_measure N hp₂ hp₂' hS
  have hmono : ∀ᶠ m in atTop,
      (wiredFiniteMeasure d m hp₁ hp₁' (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
        ≤ (wiredFiniteMeasure d m hp₂ hp₂' (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
    filter_upwards [eventually_ge_atTop N] with m hNm
    exact wiredFiniteMeasure_real_monotone_in_p_inner N m hNm hp₁ hp₁' hp₂ hp₂' hle hS
  exact le_of_tendsto_of_tendsto hlim₁ hlim₂ hmono

end StatMech.FK
