/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.FK.FKMixingUpperClose
import Code.FK.CylinderDecayClose
import Code.FK.MonotoneVolumeLimit
import Code.FK.MonotoneWeakLimit

open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}





theorem ftb_fmu_eq_cdc_multiOpen (T : Finset (Sym2 (Site d))) :
    fmu_multiOpen T = cdc_multiOpenEvent T := rfl




theorem ftb_boxMass_multiOpen_tendsto_wired (T : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))) := by
  obtain ⟨N, t, hTt⟩ := cdc_finset_in_box T
  rw [ftb_fmu_eq_cdc_multiOpen, hTt]
  exact cdc_wired_multiOpenEvent_tendsto N t hp hp1



theorem ftb_boxMass_multiOpen_tendsto_free (T : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))) := by
  obtain ⟨N, t, hTt⟩ := cdc_finset_in_box T
  rw [ftb_fmu_eq_cdc_multiOpen, hTt]
  exact cdc_free_multiOpenEvent_tendsto N t hp hp1



theorem ftb_boxProd_multiOpen_tendsto_wired (T T' : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))) :=
  (ftb_boxMass_multiOpen_tendsto_wired T hp hp1).mul (ftb_boxMass_multiOpen_tendsto_wired T' hp hp1)


theorem ftb_boxProd_multiOpen_tendsto_free (T T' : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T'))) :=
  (ftb_boxMass_multiOpen_tendsto_free T hp hp1).mul (ftb_boxMass_multiOpen_tendsto_free T' hp hp1)












theorem ftb_iv_le_box_multiOpen_wired {N m : ℕ} (hNm : N ≤ m)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen (t.image (edgeIncl d N)))
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen (t.image (edgeIncl d N))) := by
  rw [ftb_fmu_eq_cdc_multiOpen, cdc_multiOpenEvent_image_eq_boxRestrict,
    fkWiredLimit_wiredInfiniteVolume_eq N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)]
  exact fk_wired_limit_le N m hNm hp hp1 (cdc_boxMultiOpenEvent N t)



theorem ftb_multiOpen_inter (s₁ s₂ : Finset (Sym2 (Site d))) :
    fmu_multiOpen s₁ ∩ fmu_multiOpen s₂ = fmu_multiOpen (s₁ ∪ s₂) := by
  ext ω
  simp only [fmu_multiOpen, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ e (he | he)
    · exact h1 e he
    · exact h2 e he
  · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩



theorem ftb_cross_eq_multiOpen (g : Multiplicative (Site d)) (T T' : Finset (Sym2 (Site d))) :
    fmu_multiOpen T ∩
        (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
          ⁻¹' fmu_multiOpen T'
      = fmu_multiOpen (T ∪ T'.image (fun e => g⁻¹ • e)) := by
  rw [fmu_shift_multiOpen g T', ftb_multiOpen_inter]





theorem ftb_iv_le_box_multiOpen_wired_eventually (s : Finset (Sym2 (Site d)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∀ᶠ m in atTop,
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s)
        ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) := by
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  rw [Filter.eventually_atTop]
  refine ⟨N, fun m hm => ?_⟩
  rw [hst]
  exact ftb_iv_le_box_multiOpen_wired hm t hp hp1













theorem ftb_exists_common_box_wired (P : Finset (Finset (Sym2 (Site d))))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, ∀ T ∈ P, ∀ T' ∈ P,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
  classical
  
  have hev : ∀ T ∈ P, ∀ T' ∈ P, ∀ᶠ m in atTop,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    intro T _ T' _
    have htend := ftb_boxProd_multiOpen_tendsto_wired T T' hp hp1
    have := htend.eventually (Metric.ball_mem_nhds _ hδ)
    refine this.mono fun n hn => ?_
    rw [Real.dist_eq] at hn
    exact hn
  
  have hbig : ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    rw [Filter.eventually_all_finset P]
    intro T hT
    rw [Filter.eventually_all_finset P]
    intro T' hT'
    exact hev T hT T' hT'
  exact hbig.exists



theorem ftb_exists_common_box_free (P : Finset (Finset (Sym2 (Site d))))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, ∀ T ∈ P, ∀ T' ∈ P,
      |(freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
  classical
  have hev : ∀ T ∈ P, ∀ T' ∈ P, ∀ᶠ m in atTop,
      |(freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    intro T _ T' _
    have htend := ftb_boxProd_multiOpen_tendsto_free T T' hp hp1
    have := htend.eventually (Metric.ball_mem_nhds _ hδ)
    refine this.mono fun n hn => ?_
    rw [Real.dist_eq] at hn
    exact hn
  have hbig : ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      |(freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    rw [Filter.eventually_all_finset P]
    intro T hT
    rw [Filter.eventually_all_finset P]
    intro T' hT'
    exact hev T hT T' hT'
  exact hbig.exists






def ftb_FarBoxProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (μbox : ℕ → Measure (ConfigSpace (Sym2 (Site d))))
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (m : ℕ) (δ : ℝ), 0 < δ →
    ∃ g : Multiplicative (Site d), ∀ T ∈ P, ∀ T' ∈ P,
      μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T')
        ≤ (μbox m).real (fmu_multiOpen T) * (μbox m).real (fmu_multiOpen T') + δ

























def ftb_FiniteBoxDisjointProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (μbox : ℕ → Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      (μbox m).real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T')
        ≤ (μbox N).real (fmu_multiOpen T) * (μbox N).real (fmu_multiOpen T')





theorem ftb_farBoxProductDom_of_finiteBox_wired {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hfin : ftb_FiniteBoxDisjointProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))) :
    ftb_FarBoxProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  intro P N δ hδ
  obtain ⟨g, hg⟩ := hfin P N
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  
  have hivle : ∀ᶠ m in atTop,
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
        ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T') := by
    have := ftb_iv_le_box_multiOpen_wired_eventually (T ∪ T'.image (fun e => g⁻¹ • e)) hp hp1
    rw [← ftb_cross_eq_multiOpen g T T'] at this
    exact this
  
  obtain ⟨m, hivlem, hgm⟩ := (hivle.and hg).exists
  calc (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T') := hivlem
    _ ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := hgm T hT T' hT'
    _ ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ := by linarith



























theorem ftb_upperDecay_of_farBoxProductDom_wired {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdom : ftb_FarBoxProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    fmu_UpperDecay (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro P δ hδ
  
  obtain ⟨m, hm⟩ := ftb_exists_common_box_wired P hp hp1 (show (0:ℝ) < δ / 2 by linarith)
  
  obtain ⟨g, hg⟩ := hdom P m (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  have hgTT' := hg T hT T' hT'
  have hclose := hm T hT T' hT'
  
  have hboxle :
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ / 2 := by
    have := (abs_lt.mp hclose).2
    linarith
  calc (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ / 2 := hgTT'
    _ ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ / 2 + δ / 2 := by
        linarith
    _ = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ := by ring



theorem ftb_upperDecay_of_farBoxProductDom_free {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdom : ftb_FarBoxProductDom hp hp1
      (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    fmu_UpperDecay (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro P δ hδ
  obtain ⟨m, hm⟩ := ftb_exists_common_box_free P hp hp1 (show (0:ℝ) < δ / 2 by linarith)
  obtain ⟨g, hg⟩ := hdom P m (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  have hgTT' := hg T hT T' hT'
  have hclose := hm T hT T' hT'
  have hboxle :
      (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
      ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ / 2 := by
    have := (abs_lt.mp hclose).2
    linarith
  calc (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      ≤ (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ / 2 := hgTT'
    _ ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ / 2 + δ / 2 := by
        linarith
    _ = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ := by ring















theorem ftb_wiredIV_isErgodic_of_farBoxProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdom : ftb_FarBoxProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_wiredIV_isErgodic_of_upperDecay hp hp1
    (ftb_upperDecay_of_farBoxProductDom_wired hp hp1 hdom)















theorem ftb_wiredIV_isErgodic_of_finiteBoxDisjointProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hfin : ftb_FiniteBoxDisjointProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ftb_wiredIV_isErgodic_of_farBoxProductDom hp hp1
    (ftb_farBoxProductDom_of_finiteBox_wired hp hp1 hfin)





theorem ftb_freeIV_fkg_multiOpen {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (s₁ s₂ : Finset (Sym2 (Site d))) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₁)
      * (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₂)
      ≤ (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen s₁ ∩ fmu_multiOpen s₂) := by
  classical
  obtain ⟨N, t, ht⟩ := cdc_finset_in_box (s₁ ∪ s₂)
  set t₁ := t.filter (fun eb => edgeIncl d N eb ∈ s₁) with ht1
  set t₂ := t.filter (fun eb => edgeIncl d N eb ∈ s₂) with ht2
  have hsplit : ∀ (sᵢ : Finset (Sym2 (Site d))) (tᵢ : Finset (Sym2 (boxVerts d N))),
      tᵢ = t.filter (fun eb => edgeIncl d N eb ∈ sᵢ) →
      (sᵢ ⊆ s₁ ∪ s₂) → sᵢ = tᵢ.image (edgeIncl d N) := by
    intro sᵢ tᵢ htᵢ hsub
    ext e
    simp only [htᵢ, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro he
      have : e ∈ s₁ ∪ s₂ := hsub he
      rw [ht, Finset.mem_image] at this
      obtain ⟨eb, heb, rfl⟩ := this
      exact ⟨eb, ⟨heb, he⟩, rfl⟩
    · rintro ⟨eb, ⟨_, hin⟩, rfl⟩; exact hin
  have h1 : s₁ = t₁.image (edgeIncl d N) := hsplit s₁ t₁ ht1 Finset.subset_union_left
  have h2 : s₂ = t₂.image (edgeIncl d N) := hsplit s₂ t₂ ht2 Finset.subset_union_right
  have e1 : fmu_multiOpen s₁ = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t₁) := by
    rw [ftb_fmu_eq_cdc_multiOpen, h1, cdc_multiOpenEvent_image_eq_boxRestrict]
  have e2 : fmu_multiOpen s₂ = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t₂) := by
    rw [ftb_fmu_eq_cdc_multiOpen, h2, cdc_multiOpenEvent_image_eq_boxRestrict]
  rw [e1, e2]
  exact ivp_iv_fkg N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t₁)
    (cdc_boxMultiOpenEvent_isIncreasing N t₂)





theorem ftb_freeIV_isErgodic_of_farBoxProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdom : ftb_FarBoxProductDom hp hp1
      (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  set μ := (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
    : Measure (ConfigSpace (Sym2 (Site d)))) with hμdef
  have hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ :=
    bdp_freeIV_isTranslationInvariant hp hp1
  
  have hup := ftb_upperDecay_of_farBoxProductDom_free hp hp1 hdom
  
  refine fmu_freeIV_isErgodic_of_pairMixing hp hp1 ?_
  intro P δ hδ
  obtain ⟨g, hg⟩ := hup P (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  
  have hlow : μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')
      ≤ μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T') := by
    rw [fmu_shift_multiOpen g T']
    have hfkg := ftb_freeIV_fkg_multiOpen hp hp1 T (T'.image (fun e => g⁻¹ • e))
    have htrans : μ.real (fmu_multiOpen (T'.image (fun e => g⁻¹ • e)))
        = μ.real (fmu_multiOpen T') := by
      rw [← fmu_shift_multiOpen g T']
      exact fmc_real_preimage_shift hμ g (fmu_multiOpen_measurable T')
    rw [htrans] at hfkg
    exact hfkg
  have hup' := hg T hT T' hT'
  rw [abs_of_nonneg (by linarith)]
  linarith











theorem ftb_farBoxProductDom_dirac {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    [MeasurableSingletonClass (ConfigSpace (Sym2 (Site d)))] :
    ftb_FarBoxProductDom hp hp1
      (fun _ => (Measure.dirac (fun _ : Sym2 (Site d) => true)))
      (Measure.dirac (fun _ : Sym2 (Site d) => true)) := by
  intro P m δ hδ
  refine ⟨1, ?_⟩
  intro T hT T' hT'
  have hmemT : (fun _ : Sym2 (Site d) => true) ∈ fmu_multiOpen T := fun e he => rfl
  have hmemT' : (fun _ : Sym2 (Site d) => true) ∈ fmu_multiOpen T' := fun e he => rfl
  have hmemI : (fun _ : Sym2 (Site d) => true) ∈ fmu_multiOpen T ∩
      (shift (1 : Multiplicative (Site d))
        : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T' :=
    fmu_dirac_mem 1 T T'
  have hmeasT : MeasurableSet (fmu_multiOpen T) := fmu_multiOpen_measurable T
  have hmeasT' : MeasurableSet (fmu_multiOpen T') := fmu_multiOpen_measurable T'
  have hmeasI : MeasurableSet (fmu_multiOpen T ∩
      (shift (1 : Multiplicative (Site d))
        : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') :=
    hmeasT.inter (hmeasT'.preimage (measurable_shift 1))
  have e1 : (Measure.dirac (fun _ : Sym2 (Site d) => true)).real (fmu_multiOpen T) = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT, Set.indicator_of_mem hmemT]; simp
  have e2 : (Measure.dirac (fun _ : Sym2 (Site d) => true)).real (fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT', Set.indicator_of_mem hmemT']
    simp
  have eI : (Measure.dirac (fun _ : Sym2 (Site d) => true)).real (fmu_multiOpen T ∩
      (shift (1 : Multiplicative (Site d))
        : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasI, Set.indicator_of_mem hmemI]; simp
  rw [e1, e2, eI]; linarith




theorem ftb_finiteBoxDisjointProductDom_dirac {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    [MeasurableSingletonClass (ConfigSpace (Sym2 (Site d)))] :
    ftb_FiniteBoxDisjointProductDom hp hp1
      (fun _ => (Measure.dirac (fun _ : Sym2 (Site d) => true))) := by
  intro P N
  refine ⟨1, Filter.Eventually.of_forall (fun m => ?_)⟩
  intro T hT T' hT'
  have hmemT : (fun _ : Sym2 (Site d) => true) ∈ fmu_multiOpen T := fun e he => rfl
  have hmemT' : (fun _ : Sym2 (Site d) => true) ∈ fmu_multiOpen T' := fun e he => rfl
  have hmemI : (fun _ : Sym2 (Site d) => true) ∈ fmu_multiOpen T ∩
      (shift (1 : Multiplicative (Site d))
        : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T' :=
    fmu_dirac_mem 1 T T'
  have hmeasT : MeasurableSet (fmu_multiOpen T) := fmu_multiOpen_measurable T
  have hmeasT' : MeasurableSet (fmu_multiOpen T') := fmu_multiOpen_measurable T'
  have hmeasI : MeasurableSet (fmu_multiOpen T ∩
      (shift (1 : Multiplicative (Site d))
        : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') :=
    hmeasT.inter (hmeasT'.preimage (measurable_shift 1))
  have e1 : (Measure.dirac (fun _ : Sym2 (Site d) => true)).real (fmu_multiOpen T) = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT,
      Set.indicator_of_mem hmemT]; simp
  have e2 : (Measure.dirac (fun _ : Sym2 (Site d) => true)).real (fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT',
      Set.indicator_of_mem hmemT']; simp
  have eI : (Measure.dirac (fun _ : Sym2 (Site d) => true)).real (fmu_multiOpen T ∩
      (shift (1 : Multiplicative (Site d))
        : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasI, Set.indicator_of_mem hmemI]; simp
  rw [e1, e2, eI]; norm_num














theorem ftb_residue_implies_target_wired {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdom : ftb_FarBoxProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    fmu_UpperDecay (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ftb_upperDecay_of_farBoxProductDom_wired hp hp1 hdom

end FK

end StatMech
