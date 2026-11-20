/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FKGeneralQConsumer
import Code.FK.FKLimitsClose
import Code.FK.BulkDeviationProof
import Code.FK.FKMixingUpperClose
import Code.FK.InclusionExclusion

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

namespace StatMech.FK

open StatMech.IsingFK

variable {d : ℕ}


noncomputable def fkgqt_transBoxMass (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) (p q : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q)
    (flc_transEdges v N t m hNm)



theorem fkgqt_centred_eq_translated_wired (m : ℕ) (v : Site d)
    (t : Finset (Sym2 (boxVerts d m))) (p q : ℝ) :
    med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) t =
      med_multiMassProb
        (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q)
        (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (wiredFkProb (boxGraph d m) (boxBoundary d m) p q)
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q)
    (fun omega ↦ fvs_wiredFkProb_reCfgIso (boxGraph d m) (fvs_transBoxGraph d m v)
      (boxBoundary d m) (fvs_transBoxBoundary d m v) (fvs_transEquiv d m v)
      (fvs_transEquiv_adj d m v) (fvs_transEquiv_boundary d m v) p q omega)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun omega _ ↦ ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]



theorem fkgqt_centred_med_eq_measure (n : ℕ)
    (tb : Finset (Sym2 (boxVerts d n))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    med_multiMassProb
        (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) tb =
      (wiredFiniteMeasure d n hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (tb.image (edgeIncl d n))) := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict n tb]
  have hmeas : MeasurableSet
      (boxRestrict d n ⁻¹' cdc_boxMultiOpenEvent n tb) :=
    (continuous_boxRestrict d n).measurable MeasurableSet.of_discrete
  rw [fkgq_wiredFiniteMeasure_real_boxRestrictEvent n hp hp1 hq
    (cdc_boxMultiOpenEvent n tb) hmeas]
  rfl


theorem fkgqt_transBoxMass_eq_centred (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (m : ℕ) (hNm : N ≤ m) :
    fkgqt_transBoxMass v N t p q m hNm =
      (wiredFiniteMeasure d m hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [fkgqt_transBoxMass]
  unfold flc_transEdges
  rw [← fkgqt_centred_eq_translated_wired m v
    (t.image (innerEdgeLE d hNm)) p q]
  rw [fkgqt_centred_med_eq_measure m (t.image (innerEdgeLE d hNm)) hp hp1 hq]
  congr 2
  rw [Finset.image_image]
  exact Finset.image_congr (fun eb _ ↦ edgeIncl_innerEdgeLE d hNm eb)



theorem fkgqt_transBoxMass_tendsto_centred_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k : ℕ ↦ fkgqt_transBoxMass v N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  have hbase := fkgq_wired_infinite_measure N hp hp1 hq
    (cdc_boxMultiOpenEvent_isIncreasing (d := d) N t)
  rw [← cdc_multiOpenEvent_image_eq_boxRestrict N t] at hbase
  have hshift := hbase.comp (tendsto_add_atTop_nat N)
  refine hshift.congr' ?_
  filter_upwards with k
  simpa only [Function.comp_apply, Nat.add_comm] using
    (fkgqt_transBoxMass_eq_centred v N t hp hp1
      (zero_lt_one.trans_le hq) (N + k) (Nat.le_add_right N k)).symm


theorem fkgqt_squeeze_lower (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m : ℕ) (hNm : N ≤ m) (hm : 1 ≤ m) :
    (wiredFiniteMeasure d (m + flc_vrad v + 1) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e ↦ (Multiplicative.ofAdd v) • e))) ≤
      fkgqt_transBoxMass v N t p q m hNm := by
  set c := flc_vrad v with hc
  have hsub : fvs_transBox d m v ⊆ box d (m + c + 1) :=
    (flc_transBox_subset_box v m).trans (box_mono d (by omega))
  have hdom := ocd_latticeWired_multiMass_dominated
    (Sin := fvs_transBox d m v) (Sout := box d (m + c + 1))
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d (m + c + 1)) (fvs_transBoxBoundary d m v)
    (flc_hmargin_transBox_in_box v hsub) (flc_hbdryIn_transBox hm v)
    hp hp1 hq (flc_transEdges v N t m hNm)
  rw [fkgqt_transBoxMass]
  refine le_trans ?_ hdom
  change (wiredFiniteMeasure d (m + c + 1) hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
          (fun e ↦ (Multiplicative.ofAdd v) • e))) ≤
    med_multiMassProb
      (wiredFkProb (boxGraph d (m + c + 1)) (boxBoundary d (m + c + 1)) p q)
      ((flc_transEdges v N t m hNm).image (ocd_innerEdge (flc_incl hsub)))
  rw [fkgqt_centred_med_eq_measure (m + c + 1)
    ((flc_transEdges v N t m hNm).image
      (ocd_innerEdge (flc_incl hsub))) hp hp1 (zero_lt_one.trans_le hq)]
  apply le_of_eq
  congr 2
  rw [show edgeIncl d (m + c + 1) =
      Sym2.map (Subtype.val : boxVerts d (m + c + 1) → Site d) from rfl,
    flc_valImage_ocd_innerEdge_image hsub (flc_transEdges v N t m hNm),
    flc_valImage_transEdges v N t m hNm]


theorem fkgqt_squeeze_upper (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m a : ℕ) (hNm : N ≤ m) (ha : 1 ≤ a)
    (hcond : a + flc_vrad v + 1 ≤ m)
    (tb : Finset (Sym2 (boxVerts d a)))
    (htb : tb.image (edgeIncl d a) =
      (t.image (edgeIncl d N)).image (fun e ↦ (Multiplicative.ofAdd v) • e)) :
    fkgqt_transBoxMass v N t p q m hNm ≤
      (wiredFiniteMeasure d a hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
  have hsub : box d a ⊆ fvs_transBox d m v :=
    flc_box_subset_transBox v (by omega : a + flc_vrad v ≤ m)
  have hdom := ocd_latticeWired_multiMass_dominated
    (Sin := box d a) (Sout := fvs_transBox d m v)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (fvs_transBoxBoundary d m v) (boxBoundary d a)
    (flc_hmargin_box_in_transBox v hsub (by omega)) (flc_hbdryIn_box ha)
    hp hp1 hq tb
  have hkey : tb.image (ocd_innerEdge (flc_incl hsub)) =
      flc_transEdges v N t m hNm := by
    apply flc_image_eq_of_val_image_eq
    rw [flc_valImage_transEdges v N t m hNm,
      flc_valImage_ocd_innerEdge_image hsub tb,
      show Sym2.map (Subtype.val : boxVerts d a → Site d) = edgeIncl d a from rfl,
      htb]
  rw [fkgqt_transBoxMass, ← hkey]
  refine le_trans hdom ?_
  change med_multiMassProb (wiredFkProb (boxGraph d a) (boxBoundary d a) p q) tb ≤ _
  rw [fkgqt_centred_med_eq_measure a tb hp hp1 (zero_lt_one.trans_le hq), htb]


theorem fkgqt_transBoxMass_tendsto_translated_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k : ℕ ↦ fkgqt_transBoxMass v N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e ↦ (Multiplicative.ofAdd v) • e))))) := by
  classical
  let c := flc_vrad v
  let vs := (t.image (edgeIncl d N)).image
    (fun e ↦ (Multiplicative.ofAdd v) • e)
  obtain ⟨N', t', hvs⟩ := cdc_finset_in_box vs
  let L := (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)
  have hbase : Tendsto (fun r ↦
      (wiredFiniteMeasure d r hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs))
      atTop (𝓝 L) := by
    have h := fkgq_wired_infinite_measure N' hp hp1 hq
      (cdc_boxMultiOpenEvent_isIncreasing (d := d) N' t')
    rw [← cdc_multiOpenEvent_image_eq_boxRestrict N' t', ← hvs] at h
    exact h
  have hlo : Tendsto (fun k : ℕ ↦
      (wiredFiniteMeasure d ((N + k) + c + 1) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk ↦ by omega⟩
  have hhi : Tendsto (fun k : ℕ ↦
      (wiredFiniteMeasure d ((N + k) - c - 1) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + N + c + 1, fun k hk ↦ by omega⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    change _ ≤ fkgqt_transBoxMass v N t p q (N + k) _
    simpa only [vs, c] using fkgqt_squeeze_lower v N t hp hp1 hq
      (N + k) (Nat.le_add_right N k) (by omega)
  · filter_upwards [eventually_ge_atTop (N' + c + 2)] with k hk
    have hNa : N' ≤ (N + k) - c - 1 := by omega
    have ha : 1 ≤ (N + k) - c - 1 := by omega
    have hcond : ((N + k) - c - 1) + flc_vrad v + 1 ≤ N + k := by
      change ((N + k) - c - 1) + c + 1 ≤ N + k
      omega
    have htb : (t'.image (innerEdgeLE d hNa)).image
        (edgeIncl d ((N + k) - c - 1)) = vs := by
      rw [Finset.image_image]
      calc
        t'.image (edgeIncl d ((N + k) - c - 1) ∘ innerEdgeLE d hNa) =
            t'.image (edgeIncl d N') := by
              apply Finset.image_congr
              intro eb _
              exact edgeIncl_innerEdgeLE d hNa eb
        _ = vs := hvs.symm
    change fkgqt_transBoxMass v N t p q (N + k) _ ≤ _
    simpa only [vs, c] using fkgqt_squeeze_upper v N t hp hp1 hq
      (N + k) ((N + k) - c - 1) (Nat.le_add_right N k) ha hcond
      (t'.image (innerEdgeLE d hNa)) htb



theorem fkgqt_wired_multiOpen_translation (v : Site d)
    (s : Finset (Sym2 (Site d))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        (cdc_multiOpenEvent s) =
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        (cdc_multiOpenEvent (s.image
          (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
  obtain ⟨N, t, hs⟩ := cdc_finset_in_box s
  have h1 := fkgqt_transBoxMass_tendsto_centred_iv v N t hp hp1 hq
  have h2 := fkgqt_transBoxMass_tendsto_translated_iv v N t hp hp1 hq
  have hreal := tendsto_nhds_unique h1 h2
  rw [← hs] at hreal
  let μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  change (μ (cdc_multiOpenEvent s)).toReal =
    (μ (cdc_multiOpenEvent (s.image
      (fun e ↦ (Multiplicative.ofAdd v) • e)))).toReal at hreal
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top μ _) (measure_ne_top μ _)).mp hreal



theorem fkgqt_measure_eq_of_multiOpen_eq {E : Type*} [Countable E]
    (μ ν : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmom : ∀ T : Finset E, μ (fmu_multiOpen T) = ν (fmu_multiOpen T)) :
    μ = ν := by
  classical
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    obtain ⟨P, c, hexp⟩ := fmu_cylinder_expand C hC
    have hCmeas : MeasurableSet C :=
      MeasurableSet.of_mem_measurableCylinders hC
    have hμ := fmu_real_eq_sum (μ := μ) hCmeas P c hexp
    have hν := fmu_real_eq_sum (μ := ν) hCmeas P c hexp
    have hreal : μ.real C = ν.real C := by
      rw [hμ, hν]
      apply Finset.sum_congr rfl
      intro T hT
      congr 1
      unfold Measure.real
      rw [hmom T]
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top μ C) (measure_ne_top ν C)).mp hreal
  · simp



theorem fkgqt_wiredIV_isTranslationInvariant {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  let μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsProbabilityMeasure (Measure.map (shift g) μ) :=
    Measure.isProbabilityMeasure_map (measurable_shift g).aemeasurable
  refine ⟨measurable_shift g, ?_⟩
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  rw [Measure.map_apply (measurable_shift g) (fmu_multiOpen_measurable T),
    fmu_shift_multiOpen]
  simpa only [ofAdd_toAdd] using
    (fkgqt_wired_multiOpen_translation (Multiplicative.toAdd g⁻¹) T
      hp hp1 hq).symm




noncomputable def fkgqt_transBoxMassFree (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) (p q : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p q)
    (flc_transEdges v N t m hNm)



theorem fkgqt_centred_eq_translated_free (m : ℕ) (v : Site d)
    (t : Finset (Sym2 (boxVerts d m))) (p q : ℝ) :
    med_multiMassProb (fkProb (boxGraph d m) p q) t =
      med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p q)
        (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (fkProb (boxGraph d m) p q)
    (fkProb (fvs_transBoxGraph d m v) p q)
    (fun omega ↦ fvs_fkProb_reCfgIso (boxGraph d m)
      (fvs_transBoxGraph d m v) (fvs_transEquiv d m v)
      (fvs_transEquiv_adj d m v) p q omega)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun omega _ ↦ ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]



theorem fkgqt_centred_med_eq_measure_free (n : ℕ)
    (tb : Finset (Sym2 (boxVerts d n))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    med_multiMassProb (fkProb (boxGraph d n) p q) tb =
      (freeFiniteMeasure d n hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (tb.image (edgeIncl d n))) := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict n tb]
  have hmeas : MeasurableSet
      (boxRestrict d n ⁻¹' cdc_boxMultiOpenEvent n tb) :=
    (continuous_boxRestrict d n).measurable MeasurableSet.of_discrete
  rw [freeFiniteMeasure_real_boxRestrictEvent n hp hp1 hq
    (cdc_boxMultiOpenEvent n tb) hmeas]
  rfl



theorem fkgqt_transBoxMassFree_eq_centred (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (m : ℕ) (hNm : N ≤ m) :
    fkgqt_transBoxMassFree v N t p q m hNm =
      (freeFiniteMeasure d m hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [fkgqt_transBoxMassFree]
  unfold flc_transEdges
  rw [← fkgqt_centred_eq_translated_free m v
    (t.image (innerEdgeLE d hNm)) p q]
  rw [fkgqt_centred_med_eq_measure_free m
    (t.image (innerEdgeLE d hNm)) hp hp1 hq]
  congr 2
  rw [Finset.image_image]
  exact Finset.image_congr (fun eb _ ↦ edgeIncl_innerEdgeLE d hNm eb)



theorem fkgqt_transBoxMassFree_tendsto_centred_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k : ℕ ↦ fkgqt_transBoxMassFree v N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  have hbase := fkgq_free_infinite_measure N hp hp1 hq
    (cdc_boxMultiOpenEvent_isIncreasing (d := d) N t)
  rw [← cdc_multiOpenEvent_image_eq_boxRestrict N t] at hbase
  have hshift := hbase.comp (tendsto_add_atTop_nat N)
  refine hshift.congr' ?_
  filter_upwards with k
  simpa only [Function.comp_apply, Nat.add_comm] using
    (fkgqt_transBoxMassFree_eq_centred v N t hp hp1
      (zero_lt_one.trans_le hq) (N + k) (Nat.le_add_right N k)).symm


theorem fkgqt_freeSqueeze_upper (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m : ℕ) (hNm : N ≤ m) :
    fkgqt_transBoxMassFree v N t p q m hNm ≤
      (freeFiniteMeasure d (m + flc_vrad v + 1) hp hp1
        (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
  set c := flc_vrad v with hc
  have hsub : fvs_transBox d m v ⊆ box d (m + c + 1) :=
    (flc_transBox_subset_box v m).trans (box_mono d (by omega))
  have hdom := bdp_latticeFree_multiMass_dominated
    (Sin := fvs_transBox d m v) (Sout := box d (m + c + 1))
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    hp hp1 hq (flc_transEdges v N t m hNm)
  rw [fkgqt_transBoxMassFree]
  refine hdom.trans (le_of_eq ?_)
  change med_multiMassProb (fkProb (boxGraph d (m + c + 1)) p q)
      ((flc_transEdges v N t m hNm).image
        (ocd_innerEdge (flc_incl hsub))) = _
  rw [fkgqt_centred_med_eq_measure_free (m + c + 1)
    ((flc_transEdges v N t m hNm).image
      (ocd_innerEdge (flc_incl hsub))) hp hp1
      (zero_lt_one.trans_le hq)]
  congr 2
  rw [show edgeIncl d (m + c + 1) =
      Sym2.map (Subtype.val : boxVerts d (m + c + 1) → Site d) from rfl,
    flc_valImage_ocd_innerEdge_image hsub (flc_transEdges v N t m hNm),
    flc_valImage_transEdges v N t m hNm]


theorem fkgqt_freeSqueeze_lower (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (m a : ℕ) (hNm : N ≤ m)
    (hcond : a + flc_vrad v + 1 ≤ m)
    (tb : Finset (Sym2 (boxVerts d a)))
    (htb : tb.image (edgeIncl d a) =
      (t.image (edgeIncl d N)).image
        (fun e ↦ (Multiplicative.ofAdd v) • e)) :
    (freeFiniteMeasure d a hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site d)))).real
        (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
          (fun e ↦ (Multiplicative.ofAdd v) • e))) ≤
      fkgqt_transBoxMassFree v N t p q m hNm := by
  have hsub : box d a ⊆ fvs_transBox d m v :=
    flc_box_subset_transBox v (by omega : a + flc_vrad v ≤ m)
  have hdom := bdp_latticeFree_multiMass_dominated
    (Sin := box d a) (Sout := fvs_transBox d m v)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    hp hp1 hq tb
  have hkey : tb.image (ocd_innerEdge (flc_incl hsub)) =
      flc_transEdges v N t m hNm := by
    apply flc_image_eq_of_val_image_eq
    rw [flc_valImage_transEdges v N t m hNm,
      flc_valImage_ocd_innerEdge_image hsub tb,
      show Sym2.map (Subtype.val : boxVerts d a → Site d) =
        edgeIncl d a from rfl, htb]
  rw [fkgqt_transBoxMassFree, ← hkey]
  refine le_trans (le_of_eq ?_) hdom
  change _ = med_multiMassProb (fkProb (boxGraph d a) p q) tb
  rw [fkgqt_centred_med_eq_measure_free a tb hp hp1
    (zero_lt_one.trans_le hq), htb]



theorem fkgqt_transBoxMassFree_tendsto_translated_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k : ℕ ↦ fkgqt_transBoxMassFree v N t p q (N + k)
      (Nat.le_add_right N k)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e ↦ (Multiplicative.ofAdd v) • e))))) := by
  classical
  let c := flc_vrad v
  let vs := (t.image (edgeIncl d N)).image
    (fun e ↦ (Multiplicative.ofAdd v) • e)
  obtain ⟨N', t', hvs⟩ := cdc_finset_in_box vs
  let L := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)
  have hbase : Tendsto (fun r ↦
      (freeFiniteMeasure d r hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    have h := fkgq_free_infinite_measure N' hp hp1 hq
      (cdc_boxMultiOpenEvent_isIncreasing (d := d) N' t')
    rw [← cdc_multiOpenEvent_image_eq_boxRestrict N' t', ← hvs] at h
    exact h
  have hlo : Tendsto (fun k : ℕ ↦
      (freeFiniteMeasure d ((N + k) - c - 1) hp hp1
        (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + N + c + 1, fun k hk ↦ by omega⟩
  have hhi : Tendsto (fun k : ℕ ↦
      (freeFiniteMeasure d ((N + k) + c + 1) hp hp1
        (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk ↦ by omega⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (N' + c + 2)] with k hk
    have hNa : N' ≤ (N + k) - c - 1 := by omega
    have hcond : ((N + k) - c - 1) + flc_vrad v + 1 ≤ N + k := by
      change ((N + k) - c - 1) + c + 1 ≤ N + k
      omega
    have htb : (t'.image (innerEdgeLE d hNa)).image
        (edgeIncl d ((N + k) - c - 1)) = vs := by
      rw [Finset.image_image]
      calc
        t'.image (edgeIncl d ((N + k) - c - 1) ∘ innerEdgeLE d hNa) =
            t'.image (edgeIncl d N') := by
              apply Finset.image_congr
              intro eb _
              exact edgeIncl_innerEdgeLE d hNa eb
        _ = vs := hvs.symm
    change _ ≤ fkgqt_transBoxMassFree v N t p q (N + k) _
    simpa only [vs, c] using fkgqt_freeSqueeze_lower v N t hp hp1 hq
      (N + k) ((N + k) - c - 1) (Nat.le_add_right N k) hcond
      (t'.image (innerEdgeLE d hNa)) htb
  · filter_upwards with k
    change fkgqt_transBoxMassFree v N t p q (N + k) _ ≤ _
    simpa only [vs, c] using fkgqt_freeSqueeze_upper v N t hp hp1 hq
      (N + k) (Nat.le_add_right N k)



theorem fkgqt_free_multiOpen_translation (v : Site d)
    (s : Finset (Sym2 (Site d))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        (cdc_multiOpenEvent s) =
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
        (cdc_multiOpenEvent (s.image
          (fun e ↦ (Multiplicative.ofAdd v) • e))) := by
  obtain ⟨N, t, hs⟩ := cdc_finset_in_box s
  have h1 := fkgqt_transBoxMassFree_tendsto_centred_iv v N t hp hp1 hq
  have h2 := fkgqt_transBoxMassFree_tendsto_translated_iv v N t hp hp1 hq
  have hreal := tendsto_nhds_unique h1 h2
  rw [← hs] at hreal
  let μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  change (μ (cdc_multiOpenEvent s)).toReal =
    (μ (cdc_multiOpenEvent (s.image
      (fun e ↦ (Multiplicative.ofAdd v) • e)))).toReal at hreal
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top μ _) (measure_ne_top μ _)).mp hreal



theorem fkgqt_freeIV_isTranslationInvariant {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  let μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsProbabilityMeasure (Measure.map (shift g) μ) :=
    Measure.isProbabilityMeasure_map (measurable_shift g).aemeasurable
  refine ⟨measurable_shift g, ?_⟩
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  rw [Measure.map_apply (measurable_shift g) (fmu_multiOpen_measurable T),
    fmu_shift_multiOpen]
  simpa only [ofAdd_toAdd] using
    (fkgqt_free_multiOpen_translation (Multiplicative.toAdd g⁻¹) T
      hp hp1 hq).symm

end StatMech.FK
