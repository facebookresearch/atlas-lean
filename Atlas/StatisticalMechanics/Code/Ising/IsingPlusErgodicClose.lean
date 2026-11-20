/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Mathlib
import Code.FK.FKMixingUpperClose
import Code.FK.ErgodicExtremeUpgrade
import Code.Ising.IsingFKGLayer
import Code.Ising.GibbsExtreme
import Code.Ising.IsingBoxSqueeze
import Code.Ising.PlusStateTI

open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators ENNReal

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open ConfigSpace
open StatMech.FK

variable {d : ℕ}










theorem ipe_multiOpen_isClopen (T : Finset (Site d)) :
    IsClopen (fmu_multiOpen (E := Site d) T) := by
  have h : fmu_multiOpen (E := Site d) T = ⋂ e ∈ T, {ω : ConfigSpace (Site d) | ω e = true} := by
    ext ω; simp only [fmu_multiOpen, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact Set.Finite.isClopen_biInter T.finite_toSet (fun e _ => ibs_isClopen_spinUp e)




theorem ipe_cross_isClopen (g : Multiplicative (Site d)) (T T' : Finset (Site d)) :
    IsClopen (fmu_multiOpen T ∩
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' fmu_multiOpen T') :=
  (ipe_multiOpen_isClopen T).inter ((ipe_multiOpen_isClopen T').preimage (continuous_shift g))













theorem ipe_glue_preimage_increasing (η : ConfigSpace (Site d)) (n : ℕ) (T : Finset (Site d)) :
    IsIncreasing ((fun τ : {x // x ∈ box d n} → Bool => glue η τ) ⁻¹' fmu_multiOpen T) :=
  fun τ τ' hτ hmem => (fmu_multiOpen_isIncreasing T) (glue_mono_interior η τ τ' hτ) hmem








theorem ipe_fvMeasure_fkg_multiOpen (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (T₁ T₂ : Finset (Site d)) :
    (fvMeasure η n B β h).real (fmu_multiOpen T₁)
      * (fvMeasure η n B β h).real (fmu_multiOpen T₂)
      ≤ (fvMeasure η n B β h).real (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂) := by
  have hm1 := IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T₁)
  have hm2 := IsClopen.measurableSet_configSpace (ipe_multiOpen_isClopen T₂)
  have hmcap := IsClopen.measurableSet_configSpace
    ((ipe_multiOpen_isClopen T₁).inter (ipe_multiOpen_isClopen T₂))
  rw [fvMeasure_real_eq η n B β h hm1, fvMeasure_real_eq η n B β h hm2,
      fvMeasure_real_eq η n B β h hmcap]
  set A₁ := (fun τ : {x // x ∈ box d n} → Bool => glue η τ) ⁻¹' fmu_multiOpen T₁ with hA1
  set A₂ := (fun τ : {x // x ∈ box d n} → Bool => glue η τ) ⁻¹' fmu_multiOpen T₂ with hA2
  
  have hre : ∀ (S : Set (ConfigSpace (Site d))) (τ : {x // x ∈ box d n} → Bool),
      Set.indicator S (fun _ => (1:ℝ)) (glue η τ)
        = Set.indicator ((fun τ => glue η τ) ⁻¹' S) (fun _ => (1:ℝ)) τ := by
    intro S τ
    by_cases hmem : glue η τ ∈ S
    · rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (show τ ∈ (fun τ => glue η τ) ⁻¹' S from hmem)]
    · rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (show τ ∉ (fun τ => glue η τ) ⁻¹' S from hmem)]
  simp_rw [hre]
  have hcappre :
      (fun τ : {x // x ∈ box d n} → Bool => glue η τ) ⁻¹' (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂)
        = A₁ ∩ A₂ := by rw [hA1, hA2, Set.preimage_inter]
  rw [hcappre]
  exact ifk_fvProb_positively_associated_events η n B hβ h
    (ipe_glue_preimage_increasing η n T₁) (ipe_glue_preimage_increasing η n T₂)



theorem ipe_plusMeasure_fkg_multiOpen (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (T₁ T₂ : Finset (Site d)) :
    (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₁)
      * (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₂)
      ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂) :=
  ipe_fvMeasure_fkg_multiOpen (plusField d) n (bondFinsetTouch d n) hβ h T₁ T₂













theorem ipe_plusState_fkg_multiOpen {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (T₁ T₂ : Finset (Site d)) :
    (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₁)
      * (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₂)
      ≤ (plusState d β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂) := by
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  have hc1 := hconv.tendsto_real_of_isClopen (ipe_multiOpen_isClopen T₁)
  have hc2 := hconv.tendsto_real_of_isClopen (ipe_multiOpen_isClopen T₂)
  have hccap := hconv.tendsto_real_of_isClopen
    ((ipe_multiOpen_isClopen T₁).inter (ipe_multiOpen_isClopen T₂))
  have hprod := hc1.mul hc2
  have hevent : ∀ n,
      (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₁)
        * (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₂)
        ≤ (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂) :=
    fun n => ipe_plusMeasure_fkg_multiOpen (φ n) hβ h T₁ T₂
  exact le_of_tendsto_of_tendsto hprod hccap (Filter.Eventually.of_forall hevent)














theorem ipe_plusState_pairMixing_of_upperDecay {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    fmu_PairMixing (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) := by
  classical
  set μ := (plusState d β h : Measure (ConfigSpace (Site d))) with hμdef
  intro P δ hδ
  obtain ⟨g, hg⟩ := hup P (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  have hlow : μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')
      ≤ μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' fmu_multiOpen T') := by
    rw [fmu_shift_multiOpen g T']
    have hfkg := ipe_plusState_fkg_multiOpen hβ h T (T'.image (fun e => g⁻¹ • e))
    have htrans : μ.real (fmu_multiOpen (T'.image (fun e => g⁻¹ • e)))
        = μ.real (fmu_multiOpen T') := by
      rw [← fmu_shift_multiOpen g T']
      exact fmc_real_preimage_shift hti g (fmu_multiOpen_measurable T')
    rw [htrans] at hfkg
    exact hfkg
  have hup' := hg T hT T' hT'
  rw [abs_of_nonneg (by linarith)]
  linarith










theorem ipe_plusState_isErgodic_of_upperDecay {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  fmu_isErgodic_of_pairMixing hti (ipe_plusState_pairMixing_of_upperDecay hβ h hti hup)















theorem ipe_plusState_isInvariantExtremePoint_of_upperDecay {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d)))) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  haveI : Countable (Multiplicative (Site d)) := inferInstanceAs (Countable (Site d))
  StatMech.FK.eeu_isInvariantExtremePoint_of_ergodic
    (ipe_plusState_isErgodic_of_upperDecay hβ h hti hup)















theorem ipe_upperDecay_dirac :
    fmu_UpperDecay (G := Multiplicative (Site d))
      (Measure.dirac (fun _ : Site d => true)) :=
  StatMech.FK.fmu_upperDecay_dirac




example (β h : ℝ) (hβ : 0 ≤ β)
    (hti : IsTranslationInvariant (G := Multiplicative (Site 2))
      (plusState 2 β h : Measure (ConfigSpace (Site 2))))
    (hup : fmu_UpperDecay (G := Multiplicative (Site 2))
      (plusState 2 β h : Measure (ConfigSpace (Site 2)))) :
    IsErgodic (G := Multiplicative (Site 2))
      (plusState 2 β h : Measure (ConfigSpace (Site 2))) :=
  ipe_plusState_isErgodic_of_upperDecay hβ h hti hup
























theorem ipe_fkg_lower_strict_excludes_fixedShift_decoupling {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (T T' : Finset (Site d)) :
    (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)
        * (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T')
      ≤ (plusState d β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen T ∩
            (shift (1 : Multiplicative (Site d)) : ConfigSpace (Site d) → ConfigSpace (Site d))
              ⁻¹' fmu_multiOpen T') := by
  rw [show (shift (1 : Multiplicative (Site d)) : ConfigSpace (Site d) → ConfigSpace (Site d))
        ⁻¹' fmu_multiOpen T' = fmu_multiOpen T' by rw [shift_one]; rfl]
  exact ipe_plusState_fkg_multiOpen hβ h T T'

end Ising

end StatMech
