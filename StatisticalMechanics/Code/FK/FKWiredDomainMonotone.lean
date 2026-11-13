/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.FK.FKTwoBoxDecoupling

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




















theorem fwm_wired_box_domain_monotone (N m : ℕ) (hNm : N ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNm
  
  have hanti := fkWiredLimit_antitone N hp hp1 hS
  have h := hanti (Nat.zero_le k)
  simpa using h









theorem fwm_wired_multiOpen_domain_monotone (N m : ℕ) (hNm : N ≤ m)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen (t.image (edgeIncl d N)))
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen (t.image (edgeIncl d N))) := by
  rw [ftb_fmu_eq_cdc_multiOpen, cdc_multiOpenEvent_image_eq_boxRestrict]
  exact fwm_wired_box_domain_monotone N m hNm hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t)








theorem fwm_wired_domain_monotone_of_realised {N m : ℕ} (hNm : N ≤ m)
    {s : Finset (Sym2 (Site d))} (t : Finset (Sym2 (boxVerts d N)))
    (hst : s = t.image (edgeIncl d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s)
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s) := by
  subst hst
  exact fwm_wired_multiOpen_domain_monotone N m hNm t hp hp1














theorem fwm_wired_cross_le_box_domain {N m : ℕ} (hNm : N ≤ m)
    (g : Multiplicative (Site d)) (T T' : Finset (Sym2 (Site d)))
    {t : Finset (Sym2 (boxVerts d N))}
    (hreal : T ∪ T'.image (fun e => g⁻¹ • e) = t.image (edgeIncl d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T') := by
  rw [ftb_cross_eq_multiOpen g T T']
  exact fwm_wired_domain_monotone_of_realised hNm t hreal hp hp1













































def fwm_WiredDisjointBoxFactorise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (μbox : ℕ → Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ),
    (∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N)) →
    ∃ (g : Multiplicative (Site d)) (r : ℕ), ∀ T ∈ P, ∀ T' ∈ P,
      (∃ t : Finset (Sym2 (boxVerts d (N + r))),
          T ∪ T'.image (fun e => g⁻¹ • e) = t.image (edgeIncl d (N + r)))
      ∧ (μbox (N + r)).real (fmu_multiOpen T ∩
            (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen T')
          ≤ (μbox N).real (fmu_multiOpen T) * (μbox N).real (fmu_multiOpen T')





















theorem fwm_finiteBoxDisjointProductDom_conclusion_of_factorise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hfac : fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))))
    (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ)
    (hreal : ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N)) :
    ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
  obtain ⟨g, r, hg⟩ := hfac P N hreal
  refine ⟨g, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N + r, fun m hm T hT T' hT' => ?_⟩
  obtain ⟨⟨t, hcross⟩, hfacTT'⟩ := hg T hT T' hT'
  calc (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
      ≤ (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (fmu_multiOpen T ∩
                (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                  ⁻¹' fmu_multiOpen T') :=
        fwm_wired_cross_le_box_domain hm g T T' hcross hp hp1
    _ ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := hfacTT'









theorem fwm_realised_box_mono {N₀ N : ℕ} (h : N₀ ≤ N) {s : Finset (Sym2 (Site d))}
    {t : Finset (Sym2 (boxVerts d N₀))} (hst : s = t.image (edgeIncl d N₀)) :
    s = (t.image (innerEdgeLE d h)).image (edgeIncl d N) := by
  rw [hst, Finset.image_image]
  apply Finset.image_congr
  intro e _
  simp only [Function.comp_apply, edgeIncl_innerEdgeLE]



theorem fwm_exists_realising_box (P : Finset (Finset (Sym2 (Site d)))) :
    ∃ N : ℕ, ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N) := by
  classical
  
  obtain ⟨N₀, t₀, ht₀⟩ := cdc_finset_in_box (P.sup id)
  refine ⟨N₀, fun T hT => ?_⟩
  
  have hTsub : T ⊆ P.sup id := Finset.le_sup (f := id) hT
  refine ⟨(t₀.filter (fun eb => edgeIncl d N₀ eb ∈ T)), ?_⟩
  ext e
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · intro he
    have : e ∈ P.sup id := hTsub he
    rw [ht₀, Finset.mem_image] at this
    obtain ⟨eb, heb, rfl⟩ := this
    exact ⟨eb, ⟨heb, he⟩, rfl⟩
  · rintro ⟨eb, ⟨_, hin⟩, rfl⟩; exact hin





theorem fwm_exists_common_box_ge_wired (P : Finset (Finset (Sym2 (Site d)))) (N₀ : ℕ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, N₀ ≤ m ∧ ∀ T ∈ P, ∀ T' ∈ P,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
  classical
  have hbig : ∀ᶠ m in atTop, N₀ ≤ m ∧ ∀ T ∈ P, ∀ T' ∈ P,
      |(wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        * (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')
        - (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')| < δ := by
    apply Filter.Eventually.and (Filter.eventually_ge_atTop N₀)
    rw [Filter.eventually_all_finset P]
    intro T hT
    rw [Filter.eventually_all_finset P]
    intro T' hT'
    have htend := ftb_boxProd_multiOpen_tendsto_wired T T' hp hp1
    have := htend.eventually (Metric.ball_mem_nhds _ hδ)
    refine this.mono fun n hn => ?_
    rw [Real.dist_eq] at hn
    exact hn
  obtain ⟨m, hm⟩ := hbig.exists
  exact ⟨m, hm.1, hm.2⟩


















theorem fwm_upperDecay_of_factorise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hfac : fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))) :
    fmu_UpperDecay (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  intro P δ hδ
  
  obtain ⟨N₀, hN₀⟩ := fwm_exists_realising_box P
  
  obtain ⟨N, hNge, hclose⟩ := fwm_exists_common_box_ge_wired P N₀ hp hp1 (show (0:ℝ) < δ / 2 by linarith)
  
  have hrealN : ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N) := by
    intro T hT
    obtain ⟨t₀, ht₀⟩ := hN₀ T hT
    exact ⟨t₀.image (innerEdgeLE d hNge), fwm_realised_box_mono hNge ht₀⟩
  
  obtain ⟨g, hg⟩ := fwm_finiteBoxDisjointProductDom_conclusion_of_factorise hp hp1 hfac P N hrealN
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  
  have hivle := ftb_iv_le_box_multiOpen_wired_eventually
      (T ∪ T'.image (fun e => g⁻¹ • e)) hp hp1
  rw [← ftb_cross_eq_multiOpen g T T'] at hivle
  
  obtain ⟨m, hivlem, hgm⟩ := (hivle.and hg).exists
  have hgmTT' := hgm T hT T' hT'
  have hcloseTT' := (abs_lt.mp (hclose T hT T' hT')).2
  
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
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := hgmTT'
    _ ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') + δ := by linarith















theorem fwm_wiredIV_isErgodic_of_factorise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hfac : fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_wiredIV_isErgodic_of_upperDecay hp hp1 (fwm_upperDecay_of_factorise hp hp1 hfac)












theorem fwm_wiredDisjointBoxFactorise_dirac {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    [MeasurableSingletonClass (ConfigSpace (Sym2 (Site d)))] :
    fwm_WiredDisjointBoxFactorise hp hp1
      (fun _ => (Measure.dirac (fun _ : Sym2 (Site d) => true))) := by
  classical
  intro P N hreal
  
  refine ⟨1, 0, fun T hT T' hT' => ?_⟩
  refine ⟨?_, ?_⟩
  · 
    
    obtain ⟨tT, htT⟩ := hreal T hT
    obtain ⟨tT', htT'⟩ := hreal T' hT'
    refine ⟨(tT ∪ tT').image (innerEdgeLE d (Nat.le_add_right N 0)), ?_⟩
    have h1 : T'.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = T' := by
      ext e; simp only [Finset.mem_image]; constructor
      · rintro ⟨a, ha, rfl⟩; simpa using ha
      · intro he; exact ⟨e, he, by simp⟩
    rw [h1, htT, htT', ← Finset.image_union, Finset.image_image]
    apply Finset.image_congr
    intro e _
    simp only [Function.comp_apply, edgeIncl_innerEdgeLE]
  · 
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
      rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT', Set.indicator_of_mem hmemT']; simp
    have eI : (Measure.dirac (fun _ : Sym2 (Site d) => true)).real (fmu_multiOpen T ∩
        (shift (1 : Multiplicative (Site d))
          : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen T') = 1 := by
      rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasI, Set.indicator_of_mem hmemI]; simp
    rw [e1, e2, eI]; norm_num

















theorem fwm_residue_implies_target_conclusion_wired {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hfac : fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))))
    (P : Finset (Finset (Sym2 (Site d)))) (N : ℕ)
    (hreal : ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d N)), T = t.image (edgeIncl d N)) :
    ∃ g : Multiplicative (Site d), ∀ᶠ m in atTop, ∀ T ∈ P, ∀ T' ∈ P,
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') :=
  fwm_finiteBoxDisjointProductDom_conclusion_of_factorise hp hp1 hfac P N hreal

end FK

end StatMech
