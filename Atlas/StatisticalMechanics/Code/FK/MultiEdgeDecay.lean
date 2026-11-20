/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































































import Code.FK.CylinderDecayClose
import Code.FK.OffCentreCarrier

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}










def med_genericMultiOpenEvent {V : Type*} (t : Finset (Sym2 V)) :
    Set (ConfigSpace (Sym2 V)) :=
  {ω | ∀ e ∈ t, ω e = true}


theorem med_boxMultiOpenEvent_eq (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_boxMultiOpenEvent N t = med_genericMultiOpenEvent t := rfl



theorem med_genericMultiOpenEvent_increasing {V : Type*} (t : Finset (Sym2 V)) :
    IsIncreasing (med_genericMultiOpenEvent t) := by
  intro a b hab ha e he
  have hle := hab e
  rw [ha e he] at hle
  exact le_antisymm (by simp) hle





theorem med_reCfgIso_preimage {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (σ : V ≃ W) (t : Finset (Sym2 V)) :
    reCfgIso σ ⁻¹' (med_genericMultiOpenEvent t)
      = med_genericMultiOpenEvent (t.image (Sym2.map σ)) := by
  ext ω
  simp only [Set.mem_preimage, med_genericMultiOpenEvent, Set.mem_setOf_eq, reCfgIso,
    Finset.forall_mem_image]

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def med_multiMassProb (μ : ConfigSpace (Sym2 V) → ℝ) (t : Finset (Sym2 V)) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V),
    (med_genericMultiOpenEvent t).indicator (fun _ => (1:ℝ)) ω * μ ω
















theorem med_centred_mass_eq (m : ℕ) (t : Finset (Sym2 (boxVerts d m))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d m)))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict m t]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' (cdc_boxMultiOpenEvent m t)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (cdc_boxMultiOpenEvent m t) hmeas]
  rfl



theorem med_free_centred_mass_eq (m : ℕ) (t : Finset (Sym2 (boxVerts d m))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d m)))
      = med_multiMassProb (fkProb (boxGraph d m) p 2) t := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict m t]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' (cdc_boxMultiOpenEvent m t)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) (cdc_boxMultiOpenEvent m t)
    hmeas]
  rfl

























theorem med_centred_eq_translated_wired (m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m)))
    {p : ℝ} :
    med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t
      = med_multiMassProb
          (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
          (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
    (fun ω => fvs_wiredFkProb_reCfgIso (boxGraph d m) (fvs_transBoxGraph d m v)
      (boxBoundary d m) (fvs_transBoxBoundary d m v) (fvs_transEquiv d m v)
      (fvs_transEquiv_adj d m v) (fvs_transEquiv_boundary d m v) p 2 ω)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]




theorem med_centred_eq_translated_free (m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m)))
    {p : ℝ} :
    med_multiMassProb (fkProb (boxGraph d m) p 2) t
      = med_multiMassProb
          (fkProb (fvs_transBoxGraph d m v) p 2)
          (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (fkProb (boxGraph d m) p 2)
    (fkProb (fvs_transBoxGraph d m v) p 2)
    (fun ω => fvs_fkProb_reCfgIso (boxGraph d m) (fvs_transBoxGraph d m v)
      (fvs_transEquiv d m v) (fvs_transEquiv_adj d m v) p 2 ω)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]











theorem med_centred_tendsto_iv (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) :=
  cdc_wired_multiOpenEvent_tendsto N t hp hp1



theorem med_free_centred_tendsto_iv (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) :=
  cdc_free_multiOpenEvent_tendsto N t hp hp1












theorem med_edgeIncl_innerEdgeLE (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N)) :
    edgeIncl d m (innerEdgeLE d hNm eb) = edgeIncl d N eb := by
  unfold edgeIncl innerEdgeLE
  rw [Sym2.map_map]
  congr 1




theorem med_multiEvent_lift (N m : ℕ) (hNm : N ≤ m) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_multiOpenEvent ((t.image (innerEdgeLE d hNm)).image (edgeIncl d m))
      = cdc_multiOpenEvent (t.image (edgeIncl d N)) := by
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact med_edgeIncl_innerEdgeLE N m hNm eb




theorem med_centred_mass_lift (N m : ℕ) (hNm : N ≤ m) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (t.image (innerEdgeLE d hNm)) := by
  rw [← med_multiEvent_lift N m hNm t, med_centred_mass_eq m (t.image (innerEdgeLE d hNm)) hp hp1]














noncomputable def med_offCentreMultiCarrier (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
      (t.image (innerEdgeLE d hNm))
    - med_multiMassProb
        (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
        ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))





theorem med_offCentreMultiCarrier_eq_zero (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) :
    med_offCentreMultiCarrier v N t p m hNm = 0 := by
  unfold med_offCentreMultiCarrier
  rw [← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm)), sub_self]







theorem med_offCentreMultiCarrier_squeeze (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) :
    Tendsto (fun m : ℕ => med_offCentreMultiCarrier v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 0) := by
  have hzero : (fun m : ℕ => med_offCentreMultiCarrier v N t p (N + m) (Nat.le_add_right N m))
      = fun _ => (0:ℝ) := by
    funext m; exact med_offCentreMultiCarrier_eq_zero v N t p (N + m) (Nat.le_add_right N m)
  rw [hzero]
  exact tendsto_const_nhds





























theorem med_wiredMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
        med_multiMassProb
            (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
            ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
          = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
              (t'.image (innerEdgeLE d hNm))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
  
  have hCs := med_centred_tendsto_iv N t hp hp1
  
  have hCs' := med_centred_tendsto_iv N t' hp hp1
  
  have heqradius : ∀ᶠ m in atTop,
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N)))
        = (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
    filter_upwards [htrans, eventually_ge_atTop N] with m htr hNm
    
    rw [med_centred_mass_lift N m hNm t hp hp1, med_centred_mass_lift N m hNm t' hp hp1]
    
    rw [med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]
    
    exact htr hNm
  
  have hCs_to_s' : Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N))))) :=
    hCs'.congr' (heqradius.mono fun m h => h.symm)
  exact tendsto_nhds_unique hCs hCs_to_s'




theorem med_freeMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
        med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
            ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
          = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
  have hCs := med_free_centred_tendsto_iv N t hp hp1
  have hCs' := med_free_centred_tendsto_iv N t' hp hp1
  have heqradius : ∀ᶠ m in atTop,
      (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N)))
        = (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
    filter_upwards [htrans, eventually_ge_atTop N] with m htr hNm
    rw [← med_multiEvent_lift N m hNm t, med_free_centred_mass_eq m (t.image (innerEdgeLE d hNm))
        hp hp1,
      ← med_multiEvent_lift N m hNm t', med_free_centred_mass_eq m (t'.image (innerEdgeLE d hNm))
        hp hp1,
      med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]
    exact htr hNm
  have hCs_to_s' : Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N))))) :=
    hCs'.congr' (heqradius.mono fun m h => h.symm)
  exact tendsto_nhds_unique hCs hCs_to_s'











theorem med_relift_event (N₀ N : ℕ) (h : N₀ ≤ N) (t₀ : Finset (Sym2 (boxVerts d N₀))) :
    cdc_multiOpenEvent ((t₀.image (innerEdgeLE d h)).image (edgeIncl d N))
      = cdc_multiOpenEvent (t₀.image (edgeIncl d N₀)) := by
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact med_edgeIncl_innerEdgeLE N₀ N h eb















def med_wiredPlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ (∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
            med_multiMassProb
                (wiredFkProb (fvs_transBoxGraph d m (Multiplicative.toAdd g))
                  (fvs_transBoxBoundary d m (Multiplicative.toAdd g)) p 2)
                ((t.image (innerEdgeLE d hNm)).image
                  (Sym2.map (fvs_transEquiv d m (Multiplicative.toAdd g))))
              = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
                  (t'.image (innerEdgeLE d hNm)))



def med_freePlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ (∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
            med_multiMassProb (fkProb (fvs_transBoxGraph d m (Multiplicative.toAdd g)) p 2)
                ((t.image (innerEdgeLE d hNm)).image
                  (Sym2.map (fvs_transEquiv d m (Multiplicative.toAdd g))))
              = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm)))





theorem med_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : med_wiredPlacement hp hp1 g) :
    cdc_wiredMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', htrans⟩ := hplace s
  rw [show s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) from hst', hst]
  exact med_wiredMultiHomogeneous_of_cofinal (Multiplicative.toAdd g) N t t' hp hp1 htrans



theorem med_freeMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : med_freePlacement hp hp1 g) :
    cdc_freeMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', htrans⟩ := hplace s
  rw [show s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) from hst', hst]
  exact med_freeMultiHomogeneous_of_cofinal (Multiplicative.toAdd g) N t t' hp hp1 htrans











theorem med_wiredPlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, ?_⟩
  · rw [hst, Finset.image_image]
    refine Finset.image_congr fun e _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  · refine Filter.Eventually.of_forall fun m hNm => ?_
    exact (med_centred_eq_translated_wired m (Multiplicative.toAdd (1 : Multiplicative (Site d)))
      (t.image (innerEdgeLE d hNm))).symm



theorem med_freePlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_freePlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, ?_⟩
  · rw [hst, Finset.image_image]
    refine Finset.image_congr fun e _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  · refine Filter.Eventually.of_forall fun m hNm => ?_
    exact (med_centred_eq_translated_free m (Multiplicative.toAdd (1 : Multiplicative (Site d)))
      (t.image (innerEdgeLE d hNm))).symm




theorem med_wiredMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  med_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (med_wiredPlacement_one hp hp1)



theorem med_freeMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  med_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (med_freePlacement_one hp hp1)














theorem med_wiredIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), med_wiredPlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_wiredIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => med_wiredMultiHomogeneous hp hp1 g (hplace g))



theorem med_freeIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), med_freePlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_freeIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => med_freeMultiHomogeneous hp hp1 g (hplace g))

end FK

end StatMech
