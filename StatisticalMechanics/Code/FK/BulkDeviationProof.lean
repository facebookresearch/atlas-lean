/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Code.FK.UniformBulkDeviation
import Code.FK.FKLimitsClose

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false

namespace StatMech

namespace FK

variable {d : ℕ}











section FreeAbstract

variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin] [Fintype Vout] [DecidableEq Vout]
variable {Gin : SimpleGraph Vin} [DecidableRel Gin.Adj]
variable {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
variable {ιV : Vin → Vout}


def bdp_noBdry (v : Vout) : Prop := False

instance : DecidablePred (bdp_noBdry (Vout := Vout)) := fun _ => instDecidableFalse


theorem bdp_boundaryCliqueGraph_noBdry :
    StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout)) = (⊥ : SimpleGraph Vout) := by
  ext x y
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  simp [bdp_noBdry]


theorem bdp_numClustersBC_noBdry_eq (ω : ConfigSpace (Sym2 Vout)) :
    numClustersBC Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) ω
      = numClusters Gout ω := by
  rw [numClustersBC, bdp_boundaryCliqueGraph_noBdry, sup_bot_eq, numClusters,
    Nat.card_eq_fintype_card]


theorem bdp_bcWeight_noBdry_eq_fkWeight {p q : ℝ} (ω : ConfigSpace (Sym2 Vout)) :
    bcWeight Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q ω
      = fkWeight Gout p q ω := by
  rw [bcWeight, fkWeight, bdp_numClustersBC_noBdry_eq]


theorem bdp_bcProb_noBdry_eq_fkProb {p q : ℝ} (ρ : ConfigSpace (Sym2 Vout)) :
    bcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q ρ
      = fkProb Gout p q ρ := by
  have hZ : bcZ Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q
      = fkZ Gout p q := by
    rw [bcZ, fkZ]
    exact Finset.sum_congr rfl (fun ω _ => bdp_bcWeight_noBdry_eq_fkWeight ω)
  rw [bcProb, fkProb, bdp_bcWeight_noBdry_eq_fkWeight, hZ]





theorem bdp_condBcProb_innerRestrict_ge (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * fkProb Gin p q ω)
      ≤ ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
          * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q
              (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox hι hadjm hp hp1 hq0 ψ (ocd_innerRestrict ιV ⁻¹' A)]
  have hpre : ocd_psiExt ιV ψ ⁻¹' (ocd_innerRestrict ιV ⁻¹' A) = A := by
    ext ω
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hι]
  rw [hpre]
  
  have hfree : (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * fkProb Gin p q ω)
      = ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * bcProb Gin (⊥ : SimpleGraph Vin) p q ω :=
    (Finset.sum_congr rfl (fun ω _ => by rw [bcProb_bot_eq_fkProb])).symm
  rw [hfree]
  exact bcProb_free_le Gin (ocd_inducedWiring Gout ιV (bdp_noBdry (Vout := Vout)) ψ) hp hp1 hq hA





theorem bdp_free_inner_dominated_fkProb (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * fkProb Gin p q ω)
      ≤ ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * fkProb Gout p q ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * fkProb Gin p q ω with hc
  
  have hrhs : (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * fkProb Gout p q ρ)
      = ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
          * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q ρ :=
    (Finset.sum_congr rfl (fun ρ _ => by rw [bdp_bcProb_noBdry_eq_fkProb])).symm
  rw [hrhs, ocd_bcProb_decompose hι hp hp1 hq0 (ocd_innerRestrict ιV ⁻¹' A)]
  
  calc c = (∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
              (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
                bcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q σ))
            * c := by
        rw [ocd_sum_fibreMass_eq_one hι hp hp1 hq0, one_mul]
    _ = ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
            (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
              bcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q σ)
            * c := by rw [Finset.sum_mul]
    _ ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
            (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
              bcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q σ)
            * (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
                * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout)))
                    p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) := by
        apply Finset.sum_le_sum
        intro ψ _
        apply mul_le_mul_of_nonneg_left
          (hc ▸ bdp_condBcProb_innerRestrict_ge hι hadjm hp hp1 hq ψ hA)
        exact Finset.sum_nonneg (fun σ _ =>
          bcProb_nonneg Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout)))
            hp hp1 hq0 σ)

end FreeAbstract










variable {Sin Sout : Set (Site d)}











theorem bdp_latticeFree_multiMass_dominated [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) (hιinj : Function.Injective ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (Sym2 {y : Site d // y ∈ Sin})) :
    med_multiMassProb
        (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p q) t
      ≤ med_multiMassProb
          (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p q)
          (t.image (ocd_innerEdge ιV)) := by
  have hadjm := ocd_latticeAdjMatch ιV hιval
  have hdom := bdp_free_inner_dominated_fkProb (Gin := SimpleGraph.comap Subtype.val (hypercubicLattice d))
    (Gout := SimpleGraph.comap Subtype.val (hypercubicLattice d)) hιinj hadjm hp hp1 hq
    (A := med_genericMultiOpenEvent t) (med_genericMultiOpenEvent_increasing t)
  rw [ocd_innerRestrict_preimage_multiOpenEvent hιinj t] at hdom
  exact hdom











theorem bdp_centred_med_eq_measure_free (n : ℕ) (tb : Finset (Sym2 (boxVerts d n))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    med_multiMassProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p 2) tb
      = (freeFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (tb.image (edgeIncl d n))) :=
  (med_free_centred_mass_eq n tb hp hp1).symm






theorem bdp_freeSqueeze_upper (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMassFree v N t p m hNm
      ≤ (freeFiniteMeasure d (m + flc_vrad v + 1) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
              (fun e => (Multiplicative.ofAdd v) • e))) := by
  set c := flc_vrad v with hc
  have hsub : fvs_transBox d m v ⊆ box d (m + c + 1) :=
    (flc_transBox_subset_box v m).trans (box_mono d (by omega))
  
  have hdom := bdp_latticeFree_multiMass_dominated (Sin := fvs_transBox d m v)
    (Sout := box d (m + c + 1)) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    hp hp1 (by norm_num : (1:ℝ) ≤ 2) (flc_transEdges v N t m hNm)
  
  rw [show lmc_transBoxMassFree v N t p m hNm
        = med_multiMassProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p 2)
            (flc_transEdges v N t m hNm) from rfl]
  refine hdom.trans (le_of_eq ?_)
  
  rw [bdp_centred_med_eq_measure_free (m + c + 1)
        (flc_transEdges v N t m hNm |>.image (ocd_innerEdge (flc_incl hsub))) hp hp1]
  congr 2
  rw [show (edgeIncl d (m + c + 1))
        = (Sym2.map (Subtype.val : boxVerts d (m + c + 1) → Site d)) from rfl,
    flc_valImage_ocd_innerEdge_image hsub (flc_transEdges v N t m hNm),
    flc_valImage_transEdges v N t m hNm]







theorem bdp_freeSqueeze_lower (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m a : ℕ) (hNm : N ≤ m)
    (hcond : a + flc_vrad v + 1 ≤ m)
    (tb_a : Finset (Sym2 (boxVerts d a)))
    (htb : tb_a.image (edgeIncl d a)
      = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)) :
    (freeFiniteMeasure d a hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e => (Multiplicative.ofAdd v) • e)))
      ≤ lmc_transBoxMassFree v N t p m hNm := by
  set c := flc_vrad v with hc
  have hsub : box d a ⊆ fvs_transBox d m v :=
    flc_box_subset_transBox v (by omega : a + flc_vrad v ≤ m)
  
  have hdom := bdp_latticeFree_multiMass_dominated (Sin := box d a)
    (Sout := fvs_transBox d m v) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    hp hp1 (by norm_num : (1:ℝ) ≤ 2) tb_a
  
  have hkey : tb_a.image (ocd_innerEdge (flc_incl hsub)) = flc_transEdges v N t m hNm := by
    apply flc_image_eq_of_val_image_eq
    rw [flc_valImage_transEdges v N t m hNm,
      flc_valImage_ocd_innerEdge_image hsub tb_a,
      show (Sym2.map (Subtype.val : boxVerts d a → Site d)) = edgeIncl d a from rfl, htb]
  rw [show lmc_transBoxMassFree v N t p m hNm
        = med_multiMassProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p 2)
            (flc_transEdges v N t m hNm) from rfl, ← hkey]
  refine le_trans (le_of_eq ?_) hdom
  
  rw [bdp_centred_med_eq_measure_free a tb_a hp hp1, htb]










theorem bdp_transBoxMassFree_tendsto_translated_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m' : ℕ => lmc_transBoxMassFree v N t p (N + m') (Nat.le_add_right N m')) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image
            (fun e => (Multiplicative.ofAdd v) • e))))) := by
  classical
  set c := flc_vrad v with hc
  set vs := (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e) with hvs
  obtain ⟨N', t', hvs'⟩ := cdc_finset_in_box vs
  set L := (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs) with hL
  
  have hbase : Tendsto (fun r => (freeFiniteMeasure d r hp hp1 (by norm_num : (0:ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    have h := med_free_centred_tendsto_iv N' t' hp hp1
    rw [← hvs'] at h
    rw [hL]
    exact h
  
  have huptends : Tendsto (fun m' : ℕ =>
      (freeFiniteMeasure d ((N + m') + c + 1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun m' hm' => by omega⟩
  
  have hlowtends : Tendsto (fun m' : ℕ =>
      (freeFiniteMeasure d ((N + m') - c - 1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent vs)) atTop (𝓝 L) := by
    refine hbase.comp ?_
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b + N + c + 1, fun m' hm' => by omega⟩
  
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowtends huptends ?_ ?_
  · 
    filter_upwards [Filter.eventually_ge_atTop (N' + c + 2)] with m' hm'
    have hNa : N' ≤ (N + m') - c - 1 := by omega
    have hcond : ((N + m') - c - 1) + flc_vrad v + 1 ≤ (N + m') := by rw [← hc]; omega
    have htb : (t'.image (innerEdgeLE d hNa)).image (edgeIncl d ((N + m') - c - 1)) = vs := by
      have h1 : (t'.image (innerEdgeLE d hNa)).image (edgeIncl d ((N + m') - c - 1))
          = t'.image (edgeIncl d N') := by
        rw [Finset.image_image]
        exact Finset.image_congr (fun eb _ => edgeIncl_innerEdgeLE d hNa eb)
      rw [h1, hvs']
    exact bdp_freeSqueeze_lower v N t hp hp1 (N + m') ((N + m') - c - 1)
      (Nat.le_add_right N m') hcond (t'.image (innerEdgeLE d hNa)) htb
  · 
    filter_upwards with m'
    exact bdp_freeSqueeze_upper v N t hp hp1 (N + m') (Nat.le_add_right N m')











theorem bdp_freePlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) :
    lmc_freePlacement hp hp1 g := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, hst, ?_⟩
  
  have hmatch : s.image (fun e => g⁻¹ • e)
      = (t.image (edgeIncl d N)).image
          (fun e => (Multiplicative.ofAdd (Multiplicative.toAdd g⁻¹)) • e) := by
    rw [hst]
    simp only [ofAdd_toAdd]
  rw [hmatch]
  exact bdp_transBoxMassFree_tendsto_translated_iv (Multiplicative.toAdd g⁻¹) N t hp hp1


theorem bdp_freePlacement_forall {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∀ g : Multiplicative (Site d), lmc_freePlacement hp hp1 g :=
  fun g => bdp_freePlacement hp hp1 g



theorem bdp_freeMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) :
    cdc_freeMultiHomogeneous hp hp1 g :=
  lmc_freeMultiHomogeneous hp hp1 g (bdp_freePlacement hp hp1 g)





theorem bdp_freeIV_isTranslationInvariant {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  lmc_freeIV_isTranslationInvariant_of_placement hp hp1 (bdp_freePlacement_forall hp hp1)







theorem bdp_edgeMargProb_eq_med_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (μ : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    edgeMargProb μ e = med_multiMassProb μ {e} := by
  unfold edgeMargProb med_multiMassProb med_genericMultiOpenEvent
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  congr 1
  by_cases h : ω e
  · rw [if_pos h, Set.indicator_of_mem]
    intro f hf; rw [Finset.mem_singleton] at hf; subst hf; exact h
  · rw [if_neg h, Set.indicator_of_notMem]
    intro hmem; exact h (hmem e (Finset.mem_singleton_self e))








theorem bdp_measurableSet_fkEdgeOpenEvent {E : Type*} (e : E) :
    MeasurableSet (fkEdgeOpenEvent e) := by
  have : fkEdgeOpenEvent e = (fun ω : ConfigSpace E => ω e) ⁻¹' {true} := by
    ext ω; simp [fkEdgeOpenEvent]
  rw [this]
  exact (measurable_pi_apply e) (MeasurableSet.singleton true)


theorem bdp_shift_preimage_fkEdgeOpenEvent (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
        ⁻¹' (fkEdgeOpenEvent e)
      = fkEdgeOpenEvent (g⁻¹ • e) := by
  ext ω; simp [fkEdgeOpenEvent, ConfigSpace.shift]



theorem bdp_freeEdgeDensity_translation_inv {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    freeEdgeDensity d 2 e p = freeEdgeDensity d 2 (g⁻¹ • e) p := by
  unfold freeEdgeDensity
  rw [dif_pos ⟨hp, hp1, by norm_num⟩, dif_pos ⟨hp, hp1, by norm_num⟩]
  have hpre := (bdp_freeIV_isTranslationInvariant hp hp1 (d := d)).measure_preimage g
    (s := fkEdgeOpenEvent e) (bdp_measurableSet_fkEdgeOpenEvent e)
  rw [bdp_shift_preimage_fkEdgeOpenEvent g e] at hpre
  unfold Measure.real
  rw [hpre]



theorem bdp_wiredEdgeDensity_translation_inv {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    wiredEdgeDensity d 2 e p = wiredEdgeDensity d 2 (g⁻¹ • e) p := by
  unfold wiredEdgeDensity
  rw [dif_pos ⟨hp, hp1, by norm_num⟩, dif_pos ⟨hp, hp1, by norm_num⟩]
  have hpre := (flc_wiredIV_isTranslationInvariant hp hp1 (d := d)).measure_preimage g
    (s := fkEdgeOpenEvent e) (bdp_measurableSet_fkEdgeOpenEvent e)
  rw [bdp_shift_preimage_fkEdgeOpenEvent g e] at hpre
  unfold Measure.real
  rw [hpre]
















theorem bdp_free_per_edge_box_mono (a n : ℕ) (hle : a ≤ n) (eb : Sym2 (boxVerts d a)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph d a) p 2) eb
      ≤ edgeMargProb (fkProb (boxGraph d n) p 2) (innerEdgeLE d hle eb) := by
  rw [bdp_edgeMargProb_eq_med_singleton, bdp_edgeMargProb_eq_med_singleton]
  have hsub : box d a ⊆ box d n := box_mono d hle
  have hdom := bdp_latticeFree_multiMass_dominated (Sin := box d a) (Sout := box d n)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub) hp hp1
    (by norm_num : (1:ℝ) ≤ 2) ({eb} : Finset (Sym2 (boxVerts d a)))
  have hfun : ocd_innerEdge (flc_incl hsub) = innerEdgeLE d hle := by
    unfold ocd_innerEdge innerEdgeLE
    congr 1
  have himg : ({eb} : Finset (Sym2 (boxVerts d a))).image (ocd_innerEdge (flc_incl hsub))
      = {innerEdgeLE d hle eb} := by
    rw [Finset.image_singleton, hfun]
  rw [himg] at hdom
  exact hdom


theorem bdp_innerEdgeLE_refl (n : ℕ) (e : Sym2 (boxVerts d n)) :
    innerEdgeLE d (le_refl n) e = e := by
  have hfun : (boxVertInclLE d (le_refl n)) = id := by
    funext x; exact Subtype.ext rfl
  unfold innerEdgeLE
  rw [hfun, Sym2.map_id, id]







theorem bdp_free_per_edge_upper (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph d n) p 2) e
      ≤ freeEdgeDensity d 2 (edgeIncl d n e) p := by
  have h := dfi_free_per_edge_le n n (le_refl n) e hp hp1
  rwa [bdp_innerEdgeLE_refl n e] at h







theorem bdp_wired_per_edge_lower (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d n e) p
      ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) e := by
  have h := dfi_wired_per_edge_ge n n (le_refl n) e hp hp1
  rwa [bdp_innerEdgeLE_refl n e] at h






















def bdp_FreeOffCentreSandwich (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        freeEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t)
          = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧
      (∀ n, ∀ e ∈ In n,
        freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - δ n
          ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)




def bdp_WiredOffCentreSandwich (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        wiredEdgeDensity d 2 (edgeIncl d n e) (fsc_logistic t)
          = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)) ∧
      (∀ n, ∀ e ∈ In n,
        edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
          ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)





theorem bdp_freeUniformBulkDeviation_of_sandwich (N : ℕ)
    (hsand : bdp_FreeOffCentreSandwich (d := d) N) :
    ubd_FreeUniformBulkDeviation (d := d) N := by
  intro e' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hhom, hlow, hbdy⟩ := hsand e' t
  refine ⟨In, δ, hIE, hδ0, hδlim, ?_, hbdy⟩
  intro n e he
  set L := freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) with hL
  
  have hup : edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e ≤ L := by
    rw [← hhom n e he]
    exact bdp_free_per_edge_upper n e (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  
  have hlo : L - δ n ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e := hlow n e he
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩





theorem bdp_wiredUniformBulkDeviation_of_sandwich (N : ℕ)
    (hsand : bdp_WiredOffCentreSandwich (d := d) N) :
    ubd_WiredUniformBulkDeviation (d := d) N := by
  intro e' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hhom, hup, hbdy⟩ := hsand e' t
  refine ⟨In, δ, hIE, hδ0, hδlim, ?_, hbdy⟩
  intro n e he
  set L := wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) with hL
  
  have hlo : L ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e := by
    rw [← hhom n e he]
    exact bdp_wired_per_edge_lower n e (fsc_logistic_pos t) (fsc_logistic_lt_one t)
  
  have hupb : edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
      ≤ L + δ n := hup n e he
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩
















theorem bdp_fk_uniqueness_of_offCentreSandwich (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hfreeSand : bdp_FreeOffCentreSandwich (d := d) N)
    (hwiredSand : bdp_WiredOffCentreSandwich (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ubd_fk_uniqueness_of_uniformBulk hd N eb hEbox hg hboxfree
    (bdp_freeUniformBulkDeviation_of_sandwich N hfreeSand)
    (bdp_wiredUniformBulkDeviation_of_sandwich N hwiredSand)

end FK

end StatMech
