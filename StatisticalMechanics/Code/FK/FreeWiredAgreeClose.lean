/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.FK.FreeIVErgodicClose
import Code.FK.EdgeConfigZ
import Code.FK.FKUniquenessSkeleton
import Code.FK.SecantClose
import Code.FK.CylinderDecayClose
import Code.FK.FKTwoBoxDecoupling
import Code.FK.CrossBoxGeneralKeystone
import Code.FK.FKLimitsErgodicUncond

open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}










theorem fwa_freeIV_congr (d : ℕ) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp1₁ : p₁ < 1)
    (hp₂ : 0 < p₂) (hp1₂ : p₂ < 1) (heq : p₁ = p₂) :
    (freeInfiniteVolume d hp₁ hp1₁ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d))))
    = (freeInfiniteVolume d hp₂ hp1₂ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))) := by subst heq; rfl


theorem fwa_wiredIV_congr (d : ℕ) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hp1₁ : p₁ < 1)
    (hp₂ : 0 < p₂) (hp1₂ : p₂ < 1) (heq : p₁ = p₂) :
    (wiredInfiniteVolume d hp₁ hp1₁ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d))))
    = (wiredInfiniteVolume d hp₂ hp1₂ (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))) := by subst heq; rfl





theorem fwa_eventMassProb_free_at_p (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_freeMass d N (fsc_logit p)) A
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
  rw [fuc_eventMassProb_free,
    fwa_freeIV_congr d (fsc_logistic_pos _) (fsc_logistic_lt_one _) hp hp1
      (fsc_logistic_logit hp hp1)]



theorem fwa_eventMassProb_wired_at_p (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_wiredMass d N (fsc_logit p)) A
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
  rw [fuc_eventMassProb_wired,
    fwa_wiredIV_congr d (fsc_logistic_pos _) (fsc_logistic_lt_one _) hp hp1
      (fsc_logistic_logit hp hp1)]












theorem fwa_edgeIncl_boxVertInclLE {N m : ℕ} (h : N ≤ m) (e : Sym2 (boxVerts d N)) :
    edgeIncl d m (Sym2.map (boxVertInclLE d h) e) = edgeIncl d N e := by
  unfold edgeIncl
  rw [Sym2.map_map]
  congr 1




theorem fwa_rerealise {N m : ℕ} (h : N ≤ m) (t₀ : Finset (Sym2 (boxVerts d N))) :
    t₀.image (edgeIncl d N) = (t₀.image (Sym2.map (boxVertInclLE d h))).image (edgeIncl d m) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro e _
  simp only [Function.comp_apply]
  exact (fwa_edgeIncl_boxVertInclLE h e).symm











def fwa_badTilt (d N : ℕ) : Set ℝ :=
  {t | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
    eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}



theorem fwa_badTilt_countable (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) :
    (fwa_badTilt d N).Countable := by
  obtain ⟨eb, heb⟩ := Finset.card_pos.mp (ecz_box_edge_pos d hd hN)
  exact ecz_fk_uniqueness hd N eb heb




def fwa_badP (d : ℕ) : Set ℝ :=
  ⋃ N : ℕ, fsc_logistic '' (fwa_badTilt d (N + 1))



theorem fwa_badP_countable (hd : 1 ≤ d) : (fwa_badP d).Countable :=
  Set.countable_iUnion (fun N =>
    (fwa_badTilt_countable hd (Nat.le_add_left 1 N)).image _)









theorem fwa_box_agree (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hbad : p ∉ fwa_badP d)
    {N : ℕ} (hN : 1 ≤ N) {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
  rw [← fwa_eventMassProb_free_at_p, ← fwa_eventMassProb_wired_at_p]
  by_contra hne
  apply hbad
  rw [fwa_badP, Set.mem_iUnion]
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  exact ⟨M, fsc_logit p, ⟨A, hA, hne⟩, fsc_logistic_logit hp hp1⟩









theorem fwa_multiOpen_agree (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ fwa_badP d) (T : Finset (Sym2 (Site d))) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) := by
  obtain ⟨N₀, t₀, hT⟩ := cdc_finset_in_box T
  set m := max N₀ 1 with hm
  have hN₀m : N₀ ≤ m := le_max_left _ _
  have hm1 : 1 ≤ m := le_max_right _ _
  set t₁ := t₀.image (Sym2.map (boxVertInclLE d hN₀m)) with ht₁
  have hTm : T = t₁.image (edgeIncl d m) := by
    rw [hT, ht₁]; exact fwa_rerealise hN₀m t₀
  have hev : fmu_multiOpen T = boxRestrict d m ⁻¹' (cdc_boxMultiOpenEvent m t₁) := by
    rw [hTm, ftb_fmu_eq_cdc_multiOpen, cdc_multiOpenEvent_image_eq_boxRestrict m t₁]
  rw [hev]
  exact fwa_box_agree hd hp hp1 hbad hm1 (cdc_boxMultiOpenEvent_isIncreasing m t₁)













theorem fwa_FreeWiredAgree (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ fwa_badP d) :
    fie_FreeWiredAgree (d := d) hp hp1 := by
  refine ⟨fun T => fwa_multiOpen_agree hd hp hp1 hbad T, fun g T T' => ?_⟩
  rw [ftb_cross_eq_multiOpen g T T']
  exact fwa_multiOpen_agree hd hp hp1 hbad _





theorem fwa_freeIV_isErgodic (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ fwa_badP d) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fie_freeIV_isErgodic_of_agree hd hp hp1 (fwa_FreeWiredAgree hd hp hp1 hbad)












theorem fwa_fk_limits (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ fwa_badP d) :
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
              : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) :=
  feu_fk_limits_of_freeErg d hd hp hp1 (fwa_freeIV_isErgodic hd hp hp1 hbad)







theorem fwa_Ioo_not_countable : ¬ (Set.Ioo (0:ℝ) 1).Countable := by
  intro h
  rw [Set.countable_coe_iff.symm] at h
  have hlt : Cardinal.aleph0 < Cardinal.mk (Set.Ioo (0:ℝ) 1) := by
    rw [Cardinal.mk_Ioo_real (by norm_num : (0:ℝ) < 1)]
    exact Cardinal.aleph0_lt_continuum
  exact absurd (Cardinal.mk_le_aleph0_iff.mpr h) (not_le.mpr hlt)





theorem fwa_exists_good (hd : 1 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ p ∉ fwa_badP d := by
  have hne : (Set.Ioo (0:ℝ) 1 \ fwa_badP d).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hcon
    exact fwa_Ioo_not_countable ((fwa_badP_countable hd).mono hcon)
  obtain ⟨p, hpmem, hpbad⟩ := hne
  exact ⟨p, hpmem.1, hpmem.2, hpbad⟩

end FK

end StatMech
