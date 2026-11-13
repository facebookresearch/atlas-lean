/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Walls.fkc_rqvanhove
import Code.FK.FKUniqPerEdge
import Code.FK.FreeWeakLimit
import Code.FK.MonotoneWeakLimit

open scoped BigOperators
open MeasureTheory Filter Topology SimpleGraph Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

namespace StatMech.FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}




theorem fkgq_wiredFiniteMeasure_succ_real_innerRestrictEvent (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n))))
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d n ⁻¹' S)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n + 1))),
          (innerRestrict d n ⁻¹' S).indicator (fun _ => (1 : ℝ)) ρ
            * bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q ρ := by
  have hw : (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure _).real
        (boxRestrict d n ⁻¹' S)
      = ((wiredFkPMF (boxGraph d (n + 1)) (boxBoundary d (n + 1)) hp hp1 hq).toMeasure
          (extendEdge d (n + 1) ⁻¹' (boxRestrict d n ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n + 1)) hmeas]
  have hpre : extendEdge d (n + 1) ⁻¹' (boxRestrict d n ⁻¹' S)
      = innerRestrict d n ⁻¹' S := by
    ext ρ
    simp only [Set.mem_preimage, boxRestrict_extendEdge_succ]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d (n + 1) hp hp1 hq]
  exact Finset.sum_congr rfl (fun ρ _ => by rw [bcProb_clique_eq_wiredFkProb])


theorem fkgq_wiredFiniteMeasure_real_boxRestrictEvent (m : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (wiredFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d m) (boxBoundary d m) p q ω := by
  have hw : (wiredFiniteMeasure d m hp hp1 hq : Measure _).real (boxRestrict d m ⁻¹' S)
      = ((wiredFkPMF (boxGraph d m) (boxBoundary d m) hp hp1 hq).toMeasure
          (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext ω
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d m hp hp1 hq]


theorem fkgq_wiredFiniteMeasure_succ_le_smallerBox (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      ≤ ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  rw [fkgq_wiredFiniteMeasure_succ_real_innerRestrictEvent n hp hp1
    (zero_lt_one.trans_le hq) S hmeas]
  exact wiredSucc_bcProb_innerEvent_le n hp hp1 hq hS


theorem fkgq_freeFiniteMeasure_smallerBox_le_succ (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ (freeFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
  rw [freeFiniteMeasure_succ_real_innerRestrictEvent n hp hp1
    (zero_lt_one.trans_le hq) S hmeas]
  exact freeSucc_fkProb_innerEvent_le n hp hp1 hq hS




theorem fkgq_free_succ (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)
      ≤ (freeFiniteMeasure d (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, freeFiniteMeasure_real_boxRestrictEvent m hp hp1
    (zero_lt_one.trans_le hq) T hmeas]
  exact fkgq_freeFiniteMeasure_smallerBox_le_succ m hp hp1 hq hTinc hmeas


theorem fkgq_wired_succ (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredFiniteMeasure d (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)
      ≤ (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
    (zero_lt_one.trans_le hq) T hmeas]
  exact fkgq_wiredFiniteMeasure_succ_le_smallerBox m hp hp1 hq hTinc hmeas


theorem fkgq_free_infinite_measure (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)) atTop
      (nhds ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S))) := by
  set f := fun m => (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
    (boxRestrict d N ⁻¹' S) with hf
  have hmono : Monotone (fun k => f (N + k)) := by
    apply monotone_nat_of_le_succ
    intro k
    simpa [f, Nat.add_assoc] using
      fkgq_free_succ N (N + k) (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddAbove (Set.range fun k => f (N + k)) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact measureReal_le_one⟩
  set L := ⨆ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciSup hmono hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨ψ, hψ, hconv⟩ := freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N S)
  have hsub := hfull.comp hψ.tendsto_atTop
  have heq : L = (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' S) := tendsto_nhds_unique hsub hport
  rwa [heq] at hfull


theorem fkgq_wired_infinite_measure (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)) atTop
      (nhds ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S))) := by
  set f := fun m => (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
    (boxRestrict d N ⁻¹' S) with hf
  have hanti : Antitone (fun k => f (N + k)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [f, Nat.add_assoc] using
      fkgq_wired_succ N (N + k) (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddBelow (Set.range fun k => f (N + k)) :=
    ⟨0, by rintro x ⟨k, rfl⟩; exact measureReal_nonneg⟩
  set L := ⨅ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciInf hanti hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨ψ, hψ, hconv⟩ := wiredInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have hsub := hfull.comp hψ.tendsto_atTop
  have heq : L = (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' S) := tendsto_nhds_unique hsub hport
  rwa [heq] at hfull





theorem fkgq_ivp_eq_edgeFE (d n : ℕ) (s q : ℝ) (hq : 0 < q)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    ivp2_tiltFreeEnergy (boxGraph d n) q s
      = (ecz_NE (boxGraph d n) : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2
        + StatMech.Walls.fkc_edgeFreeEnergy d s q n := by
  unfold ivp2_tiltFreeEnergy StatMech.Walls.fkc_edgeFreeEnergy
  set p := fsc_logistic s
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hfact := ecz_factorization (boxGraph d n) p q
  have hZE : 0 < ecz_fkZEdge (boxGraph d n) p q := ecz_fkZEdge_pos _ hp0 hp1 hq
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ecz_NE (boxGraph d n) := by positivity
  rw [hfact, Real.log_mul h2.ne' hZE.ne', Real.log_pow]
  have hEne : ((boxGraph d n).edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring


theorem fkgq_centered_eq_edgeFE (d n : ℕ) (s q : ℝ) (hq : 0 < q)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    cfe_centered (boxGraph d n) q s
      = StatMech.Walls.fkc_edgeFreeEnergy d s q n
        - StatMech.Walls.fkc_edgeFreeEnergy d 0 q n := by
  unfold cfe_centered
  rw [fkgq_ivp_eq_edgeFE d n s q hq hE, fkgq_ivp_eq_edgeFE d n 0 q hq hE]
  ring


theorem fkgq_centeredConvergence (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ G : ℝ → ℝ,
      (∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s)))
        ∧ ConvexOn ℝ Set.univ G ∧ G 0 = 0 := by
  have hedge : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card :=
    fun n hn => ecz_box_edge_pos d hd hn
  have hconvEdge : ∀ s, ∃ L : ℝ,
      Tendsto (fun n => StatMech.Walls.fkc_edgeFreeEnergy d s q n) atTop (nhds L) := by
    intro s
    obtain ⟨ρ, hρ⟩ := StatMech.Walls.fkc_perEdgeDensityConverges d hd s q hq
    refine ⟨Real.log (1 + Real.exp s) - ρ, ?_⟩
    have h := hρ.const_sub (Real.log (1 + Real.exp s))
    have heq : (fun n => StatMech.Walls.fkc_edgeFreeEnergy d s q n)
        = fun n => Real.log (1 + Real.exp s) - StatMech.Walls.fkc_f d s q n := by
      funext n
      rw [StatMech.Walls.fkc_edgeFreeEnergy_eq]
      ring
    rw [heq]
    simpa using h
  have hcent : ∀ s, ∃ L : ℝ,
      Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds L) := by
    intro s
    obtain ⟨Ls, hLs⟩ := hconvEdge s
    obtain ⟨L0, hL0⟩ := hconvEdge 0
    refine ⟨Ls - L0, ?_⟩
    refine Tendsto.congr' ?_ (hLs.sub hL0)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (fkgq_centered_eq_edgeFE d n s q (zero_lt_one.trans_le hq) (hedge n hn)).symm
  classical
  let G : ℝ → ℝ := fun s => (hcent s).choose
  have hGlim : ∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s)) :=
    fun s => (hcent s).choose_spec
  refine ⟨G, hGlim, ?_, ?_⟩
  · refine ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
      (fun n => cfe_centered (boxGraph d (n + 1)) q) G
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hedge (n + 1) (by omega))) ?_
    intro s
    exact (hGlim s).comp (tendsto_add_atTop_nat 1)
  · have hzero : Tendsto (fun n => cfe_centered (boxGraph d n) q 0) atTop (nhds 0) := by
      simp only [cfe_centered_zero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hGlim 0) hzero


noncomputable def fkgq_avgDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q s : ℝ) : ℝ :=
  (1 / (G.edgeFinset.card : ℝ))
    * fkExpect G (fsc_logistic s) q (fun ω => (openCount G ω : ℝ))


theorem fkgq_avgDensity_eq_sum_edgeMarg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q s : ℝ) :
    fkgq_avgDensity G q s = (1 / (G.edgeFinset.card : ℝ)) *
      ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic s) q) e := by
  unfold fkgq_avgDensity fkExpect
  rw [show (fun ω => fkProb G (fsc_logistic s) q ω * (openCount G ω : ℝ)) =
      fun ω => dfi_openEdgeCount G.edgeFinset ω * fkProb G (fsc_logistic s) q ω from ?_]
  · rw [dfi_openEdgeCount_expect]
  · funext ω
    rw [adc_openCount_eq_sum]
    ring



theorem fkgq_freeBulkCollapse_n1 (q s : ℝ) (hq : 0 < q)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic s) q) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) /
          (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
    Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q s) atTop (nhds L) := by
  rw [← tendsto_add_atTop_iff_nat
    (f := fun n => fkgq_avgDensity (boxGraph d n) q s) 1]
  have hrepr : (fun n => fkgq_avgDensity (boxGraph d (n + 1)) q s) = fun n =>
      (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ)) *
        ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
          edgeMargProb (fkProb (boxGraph d (n + 1)) (fsc_logistic s) q) e := by
    funext n
    exact fkgq_avgDensity_eq_sum_edgeMarg (boxGraph d (n + 1)) q s
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb
      (fkProb (boxGraph d (n + 1)) (fsc_logistic s) q) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => adc_edgeMargProb_fkProb_nonneg (boxGraph d (n + 1))
      (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    (fun n e _ => adc_edgeMargProb_fkProb_le_one (boxGraph d (n + 1))
      (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))


theorem fkgq_wiredBulkCollapse_n1 (q s : ℝ) (hq : 0 < q)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n)
          (fsc_logistic s) q) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) /
          (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q s)
      atTop (nhds L) := by
  rw [← tendsto_add_atTop_iff_nat
    (f := fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q s) 1]
  have hrepr : (fun n => wpd_avgWiredDensity (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) q s) = fun n =>
      (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ)) *
        ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
          edgeMargProb (wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1))
            (fsc_logistic s) q) e := by
    funext n
    exact wpd_avgWiredDensity_eq_sum_edgeMarg
      (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb (wiredFkProb (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) (fsc_logistic s) q) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))


theorem fkgq_centered_hasDerivAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ) (hq : 0 < q)
    (hE : 0 < G.edgeFinset.card) (s : ℝ) :
    HasDerivAt (cfe_centered G q) (fkgq_avgDensity G q s) s := by
  have hbase := ivp2_tiltFreeEnergy_hasDerivAt G q hq hE s
  have hmean := ivp2_cgfMean_eq_openCount_expect G q hq s
  have hderiv : HasDerivAt (ivp2_tiltFreeEnergy G q) (fkgq_avgDensity G q s) s := by
    rw [← hmean] at hbase
    simpa [fkgq_avgDensity] using hbase
  exact hderiv.sub_const (ivp2_tiltFreeEnergy G q 0)


theorem fkgq_wiredCentered_hasDerivAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) (s : ℝ) :
    HasDerivAt (cfe_wiredCentered G bdry q) (wpd_avgWiredDensity G bdry q s) s := by
  exact (wpd_wiredTiltFreeEnergy_hasDerivAt G bdry q hq hE s).sub_const
    (wpd_wiredTiltFreeEnergy G bdry q 0)



theorem fkgq_wiredCentered_tendsto (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 1 ≤ q)
    {G : ℝ → ℝ} (s : ℝ)
    (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s))) :
    Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) q s)
      atTop (nhds (G s)) := by
  have hedge : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card :=
    fun n hn => ecz_box_edge_pos d hd hn
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  have hdiff : ∀ u : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q u
        - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q u)
      atTop (nhds 0) := by
    intro u
    have hbound : ∀ n, |ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q u
          - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q u|
        ≤ ((Finset.univ.filter (boxBoundary d (n + 1))).card : ℝ)
            / ((boxGraph d (n + 1)).edgeFinset.card : ℝ) * Real.log q := fun n =>
      wpd_tiltFreeEnergy_sub_le (boxGraph d (n + 1)) (boxBoundary d (n + 1)) hq
        (hedge (n + 1) (by omega)) u
    have hsv' := (hsv.mul_const (Real.log q)).comp (tendsto_add_atTop_nat 1)
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
      (squeeze_zero (fun n => abs_nonneg _) hbound (by simpa using hsv'))
  have hfree' := hfree.comp (tendsto_add_atTop_nat 1)
  have hcdiff : Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) q s
      - cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s)
      atTop (nhds 0) := by
    have := (hdiff s).sub (hdiff 0)
    have ht : Tendsto (fun n =>
        (ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q s
          - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s)
        - (ivp2_tiltFreeEnergy (boxGraph d (n + 1)) q 0
          - wpd_wiredTiltFreeEnergy (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q 0))
        atTop (nhds 0) := by simpa using this
    refine Tendsto.congr' ?_ ht
    filter_upwards with n
    unfold cfe_centered cfe_wiredCentered
    ring
  have hw' : Tendsto (fun n => cfe_wiredCentered (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) q s) atTop (nhds (G s)) := by
    have h := hfree'.sub hcdiff
    have ht : Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) q s
        - (cfe_centered (boxGraph d (n + 1)) q s
          - cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q s))
        atTop (nhds (G s)) := by simpa using h
    refine Tendsto.congr' ?_ ht
    filter_upwards with n
    ring
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by simpa [Nat.add_comm] using hw')




noncomputable def fkgq_freeMass (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ConfigSpace (Sym2 (boxVerts d N)) → ℝ := fun ω =>
  (freeInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
    (boxRestrict d N ⁻¹' {ω})


noncomputable def fkgq_wiredMass (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ConfigSpace (Sym2 (boxVerts d N)) → ℝ := fun ω =>
  (wiredInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
    (boxRestrict d N ⁻¹' {ω})

theorem fkgq_freeMass_nonneg (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    0 ≤ fkgq_freeMass d N q hq s := fun _ => measureReal_nonneg

theorem fkgq_wiredMass_nonneg (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    0 ≤ fkgq_wiredMass d N q hq s := fun _ => measureReal_nonneg

theorem fkgq_freeMass_sum_one (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ∑ ω, fkgq_freeMass d N q hq s ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable

theorem fkgq_wiredMass_sum_one (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ∑ ω, fkgq_wiredMass d N q hq s ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable

theorem fkgq_eventMass_free (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fkgq_freeMass d N q hq s) A
      = (freeInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
          (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fkgq_freeMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]

theorem fkgq_eventMass_wired (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fkgq_wiredMass d N q hq s) A
      = (wiredInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
          (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fkgq_wiredMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]


theorem fkgq_edgeMarg_free (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (e : Sym2 (boxVerts d N)) :
    edgeMargProb (fkgq_freeMass d N q hq s) e
      = freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic s) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fkgq_eventMass_free]
  unfold freeEdgeDensity
  rw [dif_pos ⟨fsc_logistic_pos s, fsc_logistic_lt_one s, zero_lt_one.trans_le hq⟩,
    fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]


theorem fkgq_edgeMarg_wired (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (e : Sym2 (boxVerts d N)) :
    edgeMargProb (fkgq_wiredMass d N q hq s) e
      = wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic s) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fkgq_eventMass_wired]
  unfold wiredEdgeDensity
  rw [dif_pos ⟨fsc_logistic_pos s, fsc_logistic_lt_one s, zero_lt_one.trans_le hq⟩,
    fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]


theorem fkgq_freeIV_le_wiredIV (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' A)
      ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' A) := by
  have hf := fkgq_free_infinite_measure N hp hp1 hq hA
  have hw := fkgq_wired_infinite_measure N hp hp1 hq hA
  refine le_of_tendsto_of_tendsto hf hw (Filter.Eventually.of_forall (fun m => ?_))
  exact freeFiniteMeasure_dominated d m hp hp1 hq _
    ((continuous_boxRestrict d N).measurable MeasurableSet.of_discrete)
    (fun a b hab ha => hA (monotone_boxRestrict d N hab) ha)


theorem fkgq_dominated (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    measOfMass (fkgq_freeMass d N q hq s) ≼ measOfMass (fkgq_wiredMass d N q hq s) := by
  intro A _ hA
  rw [measOfMass_real_eq_indicator_sum _ (fkgq_freeMass_nonneg d N q hq s) A,
    measOfMass_real_eq_indicator_sum _ (fkgq_wiredMass_nonneg d N q hq s) A]
  change eventMassProb (fkgq_freeMass d N q hq s) A
    ≤ eventMassProb (fkgq_wiredMass d N q hq s) A
  rw [fkgq_eventMass_free, fkgq_eventMass_wired]
  exact fkgq_freeIV_le_wiredIV d N (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq hA


theorem fkgq_hcoup (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∀ s : ℝ, ∃ P : ConfigSpace (Sym2 (boxVerts d N)) × ConfigSpace (Sym2 (boxVerts d N)) → ℝ,
      IsMonotoneCouplingFun P (fkgq_freeMass d N q hq s) (fkgq_wiredMass d N q hq s) :=
  fun s => fuc_isMonotoneCouplingFun_of_dominated
    (fkgq_freeMass_nonneg d N q hq s) (fkgq_wiredMass_nonneg d N q hq s)
    (fkgq_freeMass_sum_one d N q hq s) (fkgq_wiredMass_sum_one d N q hq s)
    (fkgq_dominated d N q hq s)




theorem fkgq_free_finite_mass_eq_edgeMarg (N m : ℕ) (hNm : N ≤ m)
    (e : Sym2 (boxVerts d N)) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (freeFiniteMeasure d m hp hp1 hq : Measure _).real
        (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = edgeMargProb (fkProb (boxGraph d m) p q) (innerEdgeLE d hNm e) := by
  set T := boxRestrictLE d hNm ⁻¹' boxEdgeOpenEvent d N e with hT
  have hTeq : T = boxEdgeOpenEvent d m (innerEdgeLE d hNm e) := by
    ext η
    simp only [hT, boxEdgeOpenEvent, Set.mem_preimage, Set.mem_setOf_eq, boxRestrictLE]
  have heq : boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, freeFiniteMeasure_real_boxRestrictEvent m hp hp1 hq T hmeas, hTeq]
  unfold edgeMargProb
  exact Finset.sum_congr rfl (fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent])


theorem fkgq_wired_finite_mass_eq_edgeMarg (N m : ℕ) (hNm : N ≤ m)
    (e : Sym2 (boxVerts d N)) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (wiredFiniteMeasure d m hp hp1 hq : Measure _).real
        (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q)
          (innerEdgeLE d hNm e) := by
  set T := boxRestrictLE d hNm ⁻¹' boxEdgeOpenEvent d N e with hT
  have hTeq : T = boxEdgeOpenEvent d m (innerEdgeLE d hNm e) := by
    ext η
    simp only [hT, boxEdgeOpenEvent, Set.mem_preimage, Set.mem_setOf_eq, boxRestrictLE]
  have heq : boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 hq T hmeas, hTeq]
  unfold edgeMargProb
  exact Finset.sum_congr rfl (fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent])


theorem fkgq_free_density_eq_limit (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N + k)) p q)
        (innerEdgeLE d (Nat.le_add_right N k) e)) atTop
      (nhds (freeEdgeDensity d q (edgeIncl d N e) p)) := by
  have hm := fkgq_free_infinite_measure N hp hp1 hq (boxEdgeOpenEvent_isIncreasing d N e)
  have hm' := hm.comp (dfi_tendsto_add_left N)
  have hdens : (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = freeEdgeDensity d q (edgeIncl d N e) p := by
    unfold freeEdgeDensity
    rw [dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩, fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]
  rw [hdens] at hm'
  refine hm'.congr (fun k => ?_)
  change (freeFiniteMeasure d (N + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e) = _
  exact fkgq_free_finite_mass_eq_edgeMarg N (N + k) (Nat.le_add_right N k) e hp hp1
    (zero_lt_one.trans_le hq)


theorem fkgq_wired_density_eq_limit (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => edgeMargProb
        (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p q)
        (innerEdgeLE d (Nat.le_add_right N k) e)) atTop
      (nhds (wiredEdgeDensity d q (edgeIncl d N e) p)) := by
  have hm := fkgq_wired_infinite_measure N hp hp1 hq (boxEdgeOpenEvent_isIncreasing d N e)
  have hm' := hm.comp (dfi_tendsto_add_left N)
  have hdens : (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = wiredEdgeDensity d q (edgeIncl d N e) p := by
    unfold wiredEdgeDensity
    rw [dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩, fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]
  rw [hdens] at hm'
  refine hm'.congr (fun k => ?_)
  change (wiredFiniteMeasure d (N + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e) = _
  exact fkgq_wired_finite_mass_eq_edgeMarg N (N + k) (Nat.le_add_right N k) e hp hp1
    (zero_lt_one.trans_le hq)


theorem fkgq_box_free_edgeMarg_inv (S : BoxSym d) (m : ℕ) (p q : ℝ)
    (e : Sym2 (boxVerts d m)) :
    edgeMargProb (fkProb (boxGraph d m) p q) (Sym2.map (S.lift m) e)
      = edgeMargProb (fkProb (boxGraph d m) p q) e :=
  fkTI_edgeMargProb_fkProb_reCfg (boxGraph d m) (S.lift m) (S.lift_adj m) p q e


theorem fkgq_box_wired_edgeMarg_inv (S : BoxSym d) (m : ℕ) (p q : ℝ)
    (e : Sym2 (boxVerts d m)) :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q)
        (Sym2.map (S.lift m) e)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) e :=
  fkTI_edgeMargProb_wiredFkProb_reCfg (boxGraph d m) (boxBoundary d m) (S.lift m)
    (S.lift_adj m) (S.lift_boundary m) p q e


theorem fkgq_free_density_boxSym (S : BoxSym d) (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N e) p
      = freeEdgeDensity d q (edgeIncl d N (Sym2.map (S.lift N) e)) p := by
  have h1 := fkgq_free_density_eq_limit N e hp hp1 hq
  have h2 := fkgq_free_density_eq_limit N (Sym2.map (S.lift N) e) hp hp1 hq
  refine tendsto_nhds_unique h1 (h2.congr (fun k => ?_))
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) e,
    fkgq_box_free_edgeMarg_inv S (N + k) p q]


theorem fkgq_wired_density_boxSym (S : BoxSym d) (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d N e) p
      = wiredEdgeDensity d q (edgeIncl d N (Sym2.map (S.lift N) e)) p := by
  have h1 := fkgq_wired_density_eq_limit N e hp hp1 hq
  have h2 := fkgq_wired_density_eq_limit N (Sym2.map (S.lift N) e) hp hp1 hq
  refine tendsto_nhds_unique h1 (h2.congr (fun k => ?_))
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) e,
    fkgq_box_wired_edgeMarg_inv S (N + k) p q]


theorem fkgq_free_per_edge_upper (n : ℕ) (e : Sym2 (boxVerts d n))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    edgeMargProb (fkProb (boxGraph d n) p q) e
      ≤ freeEdgeDensity d q (edgeIncl d n e) p := by
  have hlim := fkgq_free_density_eq_limit n e hp hp1 hq
  have hmono : Monotone (fun k =>
      (freeFiniteMeasure d (n + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d n ⁻¹' boxEdgeOpenEvent d n e)) := by
    apply monotone_nat_of_le_succ
    intro k
    simpa [Nat.add_assoc] using
      fkgq_free_succ n (n + k) (Nat.le_add_right n k) hp hp1 hq
        (boxEdgeOpenEvent_isIncreasing d n e)
  have hseq : ∀ k, edgeMargProb (fkProb (boxGraph d n) p q) e ≤
      edgeMargProb (fkProb (boxGraph d (n + k)) p q)
        (innerEdgeLE d (Nat.le_add_right n k) e) := by
    intro k
    have hk := hmono (Nat.zero_le k)
    dsimp only at hk
    rw [Nat.add_zero,
      fkgq_free_finite_mass_eq_edgeMarg n n (le_refl n) e hp hp1 (zero_lt_one.trans_le hq),
      fkgq_free_finite_mass_eq_edgeMarg n (n + k) (Nat.le_add_right n k) e hp hp1
        (zero_lt_one.trans_le hq)] at hk
    rwa [bdp_innerEdgeLE_refl n e] at hk
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hseq)


theorem fkgq_wired_per_edge_lower (n : ℕ) (e : Sym2 (boxVerts d n))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d n e) p
      ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) e := by
  have hlim := fkgq_wired_density_eq_limit n e hp hp1 hq
  have hanti : Antitone (fun k =>
      (wiredFiniteMeasure d (n + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d n ⁻¹' boxEdgeOpenEvent d n e)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [Nat.add_assoc] using
      fkgq_wired_succ n (n + k) (Nat.le_add_right n k) hp hp1 hq
        (boxEdgeOpenEvent_isIncreasing d n e)
  have hseq : ∀ k, edgeMargProb
      (wiredFkProb (boxGraph d (n + k)) (boxBoundary d (n + k)) p q)
        (innerEdgeLE d (Nat.le_add_right n k) e)
      ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) e := by
    intro k
    have hk := hanti (Nat.zero_le k)
    dsimp only at hk
    rw [Nat.add_zero,
      fkgq_wired_finite_mass_eq_edgeMarg n n (le_refl n) e hp hp1 (zero_lt_one.trans_le hq),
      fkgq_wired_finite_mass_eq_edgeMarg n (n + k) (Nat.le_add_right n k) e hp hp1
        (zero_lt_one.trans_le hq)] at hk
    rwa [bdp_innerEdgeLE_refl n e] at hk
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hseq)





theorem fkgq_free_offCentre_lower (R n : ℕ) (hRn : R ≤ n) (hmn : n - R ≤ n)
    (u v : boxVerts d (n - R)) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (c0 : (0 : Site d) ∈ box d R) (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
    edgeMargProb (fkProb (boxGraph d R) p q)
        (s((⟨(0 : Site d), c0⟩ : boxVerts d R),
          (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)))
      ≤ edgeMargProb (fkProb (boxGraph d n) p q)
          (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R)))) := by
  set a : Site d := (u : Site d) with ha
  have ha_box : a ∈ box d (n - R) := u.2
  have hsub : fvs_transBox d R a ⊆ box d n := by
    intro y hy i
    have hyi : ((y - a) i).natAbs ≤ R := hy i
    have hai : (a i).natAbs ≤ n - R := ha_box i
    have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
    have hyeq : y i = (y i - a i) + a i := by ring
    calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
      _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
      _ ≤ R + (n - R) := Nat.add_le_add hyi hai
      _ = n := by omega
  set ce : Sym2 (boxVerts d R) :=
    s((⟨(0 : Site d), c0⟩ : boxVerts d R),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)) with hce
  have htrans := (fvs_box_translation_edgeMarg d R a ce (p := p) (q := q)).2
  set eS : Sym2 (fvs_transBoxVerts d R a) := Sym2.map (fvs_transEquiv d R a) ce with heS
  have hdom := bdp_latticeFree_multiMass_dominated (Sin := fvs_transBox d R a) (Sout := box d n)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub) hp hp1 hq
    ({eS} : Finset (Sym2 (fvs_transBoxVerts d R a)))
  rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
    ← bdp_edgeMargProb_eq_med_singleton] at hdom
  rw [show edgeMargProb (fkProb (boxGraph d R) p q) ce
        = edgeMargProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p q) eS
      from htrans.symm]
  refine hdom.trans (le_of_eq ?_)
  congr 1
  exact ocs_innerEdge_recentre d R n (n - R) hmn u v hsub c0 cw



theorem fkgq_wired_offCentre_upper (R n : ℕ) (hR : 1 ≤ R) (hRn1 : R + 1 ≤ n)
    (hmn : n - R - 1 ≤ n) (u v : boxVerts d (n - R - 1))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (c0 : (0 : Site d) ∈ box d R) (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
    edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q)
        (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R - 1))))
      ≤ edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p q)
          (s((⟨(0 : Site d), c0⟩ : boxVerts d R),
            (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))) := by
  set a : Site d := (u : Site d) with ha
  have ha_box : a ∈ box d (n - R - 1) := u.2
  have hsub : fvs_transBox d R a ⊆ box d n := by
    intro y hy i
    have hyi : ((y - a) i).natAbs ≤ R := hy i
    have hai : (a i).natAbs ≤ n - R - 1 := ha_box i
    have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
    have hyeq : y i = (y i - a i) + a i := by ring
    calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
      _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
      _ ≤ R + (n - R - 1) := Nat.add_le_add hyi hai
      _ ≤ n := by omega
  set ce : Sym2 (boxVerts d R) :=
    s((⟨(0 : Site d), c0⟩ : boxVerts d R),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)) with hce
  have htrans := (fvs_box_translation_edgeMarg d R a ce (p := p) (q := q)).1
  set eS : Sym2 (fvs_transBoxVerts d R a) := Sym2.map (fvs_transEquiv d R a) ce with heS
  have hdom := ocd_latticeWired_multiMass_dominated (Sin := fvs_transBox d R a) (Sout := box d n)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d n) (fvs_transBoxBoundary d R a)
    (ocs_wired_margin d R n a ha_box hRn1 hsub) (flc_hbdryIn_transBox hR a)
    hp hp1 hq ({eS} : Finset (Sym2 (fvs_transBoxVerts d R a)))
  rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
    ← bdp_edgeMargProb_eq_med_singleton] at hdom
  rw [show edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p q) ce
        = edgeMargProb
          (wiredFkProb (fvs_transBoxGraph d R a) (fvs_transBoxBoundary d R a) p q) eS
      from htrans.symm]
  refine le_trans (le_of_eq ?_) hdom
  congr 1
  exact (ocs_innerEdge_recentre d R n (n - R - 1) hmn u v hsub c0 cw).symm




theorem fkgq_transBox_subset_box_add (m : ℕ) (a : Site d) :
    fvs_transBox d m a ⊆ box d (m + Finset.univ.sup (fun i => (a i).natAbs)) := by
  intro y hy i
  have hyi : ((y - a) i).natAbs ≤ m := hy i
  have hai : (a i).natAbs ≤ Finset.univ.sup (fun j => (a j).natAbs) :=
    Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
  have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
  have hyeq : y i = (y i - a i) + a i := by ring
  calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
    _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
    _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
    _ ≤ m + Finset.univ.sup (fun j => (a j).natAbs) := Nat.add_le_add hyi hai



theorem fkgq_density_translate_order (N : ℕ) (eb : Sym2 (boxVerts d N)) (a : Site d)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N eb) p
        ≤ freeEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p
      ∧ wiredEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p
        ≤ wiredEdgeDensity d q (edgeIncl d N eb) p := by
  induction eb with
  | h u v =>
    set C := Finset.univ.sup (fun i => (a i).natAbs) with hC
    have hua : (u : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      have hu := u.2 i
      have ha : (a i).natAbs ≤ C := by
        rw [hC]; exact Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
      exact le_trans (le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add hu ha)) (by omega)
    have hva : (v : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      have hv := v.2 i
      have ha : (a i).natAbs ≤ C := by
        rw [hC]; exact Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
      exact le_trans (le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add hv ha)) (by omega)
    set ebA : Sym2 (boxVerts d (N + C + 1)) :=
      s((⟨(u : Site d) + a, hua⟩ : boxVerts d (N + C + 1)),
        (⟨(v : Site d) + a, hva⟩ : boxVerts d (N + C + 1))) with hebA
    have hInclA : edgeIncl d (N + C + 1) ebA
        = Sym2.map (fun x => x + a) (edgeIncl d N (s(u, v))) := by
      rw [hebA]
      simp only [edgeIncl, Sym2.map_mk]
    have hfreeL := fkgq_free_density_eq_limit N (s(u, v)) hp hp1 hq
    have hfreeR := fkgq_free_density_eq_limit (N + C + 1) ebA hp hp1 hq
    have hwiredL := fkgq_wired_density_eq_limit N (s(u, v)) hp hp1 hq
    have hwiredR := fkgq_wired_density_eq_limit (N + C + 1) ebA hp hp1 hq
    have hfreeSeq : ∀ k,
        edgeMargProb (fkProb (boxGraph d (N + k)) p q)
            (innerEdgeLE d (Nat.le_add_right N k) (s(u, v)))
          ≤ edgeMargProb (fkProb (boxGraph d ((N + C + 1) + k)) p q)
            (innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA) := by
      intro k
      set m := N + k with hm
      set n := (N + C + 1) + k with hn
      have hsub : fvs_transBox d m a ⊆ box d n := by
        intro x hx i
        exact le_trans (fkgq_transBox_subset_box_add (d := d) m a hx i) (by simp [n, m, C]; omega)
      set em : Sym2 (boxVerts d m) := innerEdgeLE d (Nat.le_add_right N k) (s(u, v)) with hem
      set eS : Sym2 (fvs_transBoxVerts d m a) := Sym2.map (fvs_transEquiv d m a) em with heS
      have htrans := (fvs_box_translation_edgeMarg d m a em (p := p) (q := q)).2
      have hdom := bdp_latticeFree_multiMass_dominated (Sin := fvs_transBox d m a)
        (Sout := box d n) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
        hp hp1 hq ({eS} : Finset (Sym2 (fvs_transBoxVerts d m a)))
      rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
        ← bdp_edgeMargProb_eq_med_singleton] at hdom
      have hedge : ocd_innerEdge (flc_incl hsub) eS
          = innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA := by
        apply Sym2.map.injective (Subtype.val_injective (p := fun y => y ∈ box d n))
        simp only [eS, em, innerEdgeLE, ocd_innerEdge, Sym2.map_map, Sym2.map_mk, ebA, n, m]
        congr
      rw [← hedge]
      exact htrans.symm.trans_le hdom
    have hwiredSeq : ∀ k, 1 ≤ N + k →
        edgeMargProb (wiredFkProb (boxGraph d ((N + C + 1) + k))
            (boxBoundary d ((N + C + 1) + k)) p q)
            (innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA)
          ≤ edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p q)
            (innerEdgeLE d (Nat.le_add_right N k) (s(u, v))) := by
      intro k hm1
      set m := N + k with hm
      set n := (N + C + 1) + k with hn
      have hsub : fvs_transBox d m a ⊆ box d n := by
        intro x hx i
        exact le_trans (fkgq_transBox_subset_box_add (d := d) m a hx i) (by simp [n, m, C]; omega)
      set em : Sym2 (boxVerts d m) := innerEdgeLE d (Nat.le_add_right N k) (s(u, v)) with hem
      set eS : Sym2 (fvs_transBoxVerts d m a) := Sym2.map (fvs_transEquiv d m a) em with heS
      have htrans := (fvs_box_translation_edgeMarg d m a em (p := p) (q := q)).1
      have hmargin : ∀ x : fvs_transBoxVerts d m a, ¬ boxBoundary d n (flc_incl hsub x) := by
        intro x hbd
        have hx : (x : Site d) ∈ box d (n - 1) := by
          intro i
          exact le_trans (fkgq_transBox_subset_box_add (d := d) m a x.2 i)
            (by simp [n, m, C]; omega)
        exact hbd.2 hx
      have hdom := ocd_latticeWired_multiMass_dominated (Sin := fvs_transBox d m a)
        (Sout := box d n) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
        (boxBoundary d n) (fvs_transBoxBoundary d m a) hmargin
        (flc_hbdryIn_transBox hm1 a) hp hp1 hq
        ({eS} : Finset (Sym2 (fvs_transBoxVerts d m a)))
      rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
        ← bdp_edgeMargProb_eq_med_singleton] at hdom
      have hedge : ocd_innerEdge (flc_incl hsub) eS
          = innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA := by
        apply Sym2.map.injective (Subtype.val_injective (p := fun y => y ∈ box d n))
        simp only [eS, em, innerEdgeLE, ocd_innerEdge, Sym2.map_map, Sym2.map_mk, ebA, n, m]
        congr
      rw [← hedge]
      exact hdom.trans_eq htrans
    constructor
    · rw [← hInclA]
      exact le_of_tendsto_of_tendsto hfreeL hfreeR (Filter.Eventually.of_forall hfreeSeq)
    · rw [← hInclA]
      refine le_of_tendsto_of_tendsto hwiredR hwiredL ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      exact hwiredSeq k (by omega)


theorem fkgq_density_translation_inv (N : ℕ) (eb : Sym2 (boxVerts d N)) (a : Site d)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N eb) p
        = freeEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p
      ∧ wiredEdgeDensity d q (edgeIncl d N eb) p
        = wiredEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p := by
  obtain ⟨hf, hw⟩ := fkgq_density_translate_order N eb a hp hp1 hq
  
  induction eb with
  | h u v =>
    set C := Finset.univ.sup (fun i => (a i).natAbs)
    have hua : (u : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      exact le_trans (le_trans (Int.natAbs_add_le _ _)
        (Nat.add_le_add (u.2 i) (Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)))) (by omega)
    have hva : (v : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      exact le_trans (le_trans (Int.natAbs_add_le _ _)
        (Nat.add_le_add (v.2 i) (Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)))) (by omega)
    set ebA : Sym2 (boxVerts d (N + C + 1)) :=
      s((⟨(u : Site d) + a, hua⟩ : boxVerts d (N + C + 1)),
        (⟨(v : Site d) + a, hva⟩ : boxVerts d (N + C + 1)))
    obtain ⟨hfback, hwback⟩ :=
      fkgq_density_translate_order (d := d) (N + C + 1) ebA (-a) hp hp1 hq
    have hA : edgeIncl d (N + C + 1) ebA
        = Sym2.map (fun x => x + a) (edgeIncl d N (s(u, v))) := by
      simp [ebA, edgeIncl]
    have hback : Sym2.map (fun x => x + -a) (edgeIncl d (N + C + 1) ebA)
        = edgeIncl d N (s(u, v)) := by
      rw [hA]
      simp only [Sym2.map_map]
      change Sym2.map ((fun x => x + -a) ∘ fun x => x + a) (edgeIncl d N (s(u, v)))
        = Sym2.map id (edgeIncl d N (s(u, v)))
      apply Sym2.map_congr
      intro x _
      simp
    rw [hback] at hfback hwback
    rw [hA] at hfback hwback
    exact ⟨le_antisymm hf hfback, le_antisymm hwback hw⟩





theorem fkgq_free_density_boxSym_lattice (S : BoxSym d) (e : Sym2 (Site d))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (Sym2.map S.τ e) p = freeEdgeDensity d q e p := by
  induction e with
  | h x y =>
    let N := max (Finset.univ.sup (fun i => (x i).natAbs))
      (Finset.univ.sup (fun i => (y i).natAbs))
    have hxN : x ∈ box d N := fun i =>
      le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _)
    have hyN : y ∈ box d N := fun i =>
      le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)
    let eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N))
    have hincl : edgeIncl d N eb = s(x, y) := by simp [eb, edgeIncl]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkgq_free_density_boxSym S N eb hp hp1 hq).symm



theorem fkgq_wired_density_boxSym_lattice (S : BoxSym d) (e : Sym2 (Site d))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (Sym2.map S.τ e) p = wiredEdgeDensity d q e p := by
  induction e with
  | h x y =>
    let N := max (Finset.univ.sup (fun i => (x i).natAbs))
      (Finset.univ.sup (fun i => (y i).natAbs))
    have hxN : x ∈ box d N := fun i =>
      le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _)
    have hyN : y ∈ box d N := fun i =>
      le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)
    let eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N))
    have hincl : edgeIncl d N eb = s(x, y) := by simp [eb, edgeIncl]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkgq_wired_density_boxSym S N eb hp hp1 hq).symm



theorem fkgq_density_translation_inv_lattice (e : Sym2 (Site d)) (a : Site d)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q e p = freeEdgeDensity d q (Sym2.map (fun x => x + a) e) p ∧
      wiredEdgeDensity d q e p = wiredEdgeDensity d q (Sym2.map (fun x => x + a) e) p := by
  induction e with
  | h x y =>
    let N := max (Finset.univ.sup (fun i => (x i).natAbs))
      (Finset.univ.sup (fun i => (y i).natAbs))
    have hxN : x ∈ box d N := fun i =>
      le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _)
    have hyN : y ∈ box d N := fun i =>
      le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)
    let eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N))
    have hincl : edgeIncl d N eb = s(x, y) := by simp [eb, edgeIncl]
    simpa [hincl] using fkgq_density_translation_inv (d := d) N eb a hp hp1 hq


theorem fkgq_free_density_recentre (x y : Site d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d q (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  have h := (fkgq_density_translation_inv_lattice
    (d := d) (s(x, y) : Sym2 (Site d)) (-x) hp hp1 hq).1
  rw [h]
  congr 1
  simp only [Sym2.map_mk]
  congr <;> simp


theorem fkgq_wired_density_recentre (x y : Site d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d q (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  have h := (fkgq_density_translation_inv_lattice
    (d := d) (s(x, y) : Sym2 (Site d)) (-x) hp hp1 hq).2
  rw [h]
  congr 1
  simp only [Sym2.map_mk]
  congr <;> simp



theorem fkgq_free_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
  have hpos : freeEdgeDensity d q
      (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d q
          (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← fkgq_free_density_boxSym_lattice (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1 hq,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← fkgq_free_density_boxSym_lattice
        (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1 hq,
      rot_map_centred_edge]
  show freeEdgeDensity d q (s((0 : Site d),
      rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j)
        (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl



theorem fkgq_wired_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
  have hpos : wiredEdgeDensity d q
      (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d q
          (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← fkgq_wired_density_boxSym_lattice (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1 hq,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← fkgq_wired_density_boxSym_lattice
        (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1 hq,
      rot_map_centred_edge]
  show wiredEdgeDensity d q (s((0 : Site d),
      rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j)
        (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl


theorem fkgq_free_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [fkgq_free_density_recentre x y hp hp1 hq, hdir]
  exact fkgq_free_centred_unit_const hd j b hp hp1 hq


theorem fkgq_wired_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [fkgq_wired_density_recentre x y hp hp1 hq, hdir]
  exact fkgq_wired_centred_unit_const hd j b hp hp1 hq


theorem fkgq_free_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d m eb) p
      = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    exact fkgq_free_edge_const hd (u : Site d) (v : Site d) heb hp hp1 hq


theorem fkgq_wired_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d m eb) p
      = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    exact fkgq_wired_edge_const hd (u : Site d) (v : Site d) heb hp hp1 hq




theorem fkgq_fkExpect_openCount_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℝ) :
    fkExpect G p q (fun ω => (openCount G ω : ℝ))
      = ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G p q) e := by
  unfold fkExpect
  rw [show (fun ω => fkProb G p q ω * (openCount G ω : ℝ))
      = (fun ω => dfi_openEdgeCount G.edgeFinset ω * fkProb G p q ω) from ?_]
  · exact dfi_openEdgeCount_expect G.edgeFinset (fkProb G p q)
  · funext ω
    rw [adc_openCount_eq_sum]
    ring


theorem fkgq_avgDensity_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q t : ℝ) :
    fkgq_avgDensity G q t = (1 / (G.edgeFinset.card : ℝ))
      * ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic t) q) e := by
  unfold fkgq_avgDensity
  rw [fkgq_fkExpect_openCount_eq_sum]


theorem fkgq_free_avg_collapse (q t : ℝ) (hq : 1 ≤ q)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
      (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (nhds 0)) :
    Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop (nhds L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  rw [show (fun n => fkgq_avgDensity (boxGraph d n) q t) = fun n =>
      (1 / ((boxGraph d n).edgeFinset.card : ℝ)) * ∑ e ∈ (boxGraph d n).edgeFinset,
        edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) e from
    funext fun n => fkgq_avgDensity_eq_sum (boxGraph d n) q t]
  exact adc_absavg_tendsto
    (En := fun n => (boxGraph d n).edgeFinset) In
    (fn := fun n e => edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) e)
    L δ hIE
    (fun n e _ => adc_edgeMargProb_fkProb_nonneg (boxGraph d n) hp hp1
      (zero_lt_one.trans_le hq) e)
    (fun n e _ => adc_edgeMargProb_fkProb_le_one (boxGraph d n) hp hp1
      (zero_lt_one.trans_le hq) e)
    hL0 hL1 hδ0 hδlim hin hE hbdy


theorem fkgq_wired_avg_collapse (q t : ℝ) (hq : 1 ≤ q)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) e - L|
        ≤ δ n)
    (hbdy : Tendsto (fun n =>
      (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (nhds 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t)
      atTop (nhds L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  rw [show (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) = fun n =>
      (1 / ((boxGraph d n).edgeFinset.card : ℝ)) * ∑ e ∈ (boxGraph d n).edgeFinset,
        edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) e from
    funext fun n => wpd_avgWiredDensity_eq_sum_edgeMarg
      (boxGraph d n) (boxBoundary d n) q t]
  exact adc_absavg_tendsto
    (En := fun n => (boxGraph d n).edgeFinset) In
    (fn := fun n e => edgeMargProb
      (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) e)
    L δ hIE
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n)
      hp hp1 (zero_lt_one.trans_le hq) e)
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d n) (boxBoundary d n)
      hp hp1 (zero_lt_one.trans_le hq) e)
    hL0 hL1 hδ0 hδlim hin hE hbdy


noncomputable def fkgq_unitMarg (d : ℕ) (q : ℝ) (n : ℕ)
    (dir : Fin d × Bool) (t : ℝ) : ℝ :=
  if hR : 1 ≤ Nat.sqrt n then
    edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) (fsc_logistic t) q)
      (ocs_unitEdge d (Nat.sqrt n) hR dir)
  else 0


noncomputable def fkgq_unitWiredMarg (d : ℕ) (q : ℝ) (n : ℕ)
    (dir : Fin d × Bool) (t : ℝ) : ℝ :=
  if hR : 1 ≤ Nat.sqrt n then
    edgeMargProb (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n))
      (fsc_logistic t) q) (ocs_unitEdge d (Nat.sqrt n) hR dir)
  else 0


theorem fkgq_unitMarg_tendsto (q : ℝ) (hq : 1 ≤ q) (dir : Fin d × Bool) (t : ℝ) :
    Tendsto (fun n => fkgq_unitMarg d q n dir t) atTop
      (nhds (freeEdgeDensity d q
        (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t))) := by
  have hbase := fkgq_free_density_eq_limit (d := d) 1
    (ocs_unitEdge d 1 (le_refl 1) dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  have hmap : Tendsto (fun n : ℕ => Nat.sqrt n - 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + 1) * (b + 1), fun n hn => ?_⟩
    have : b + 1 ≤ Nat.sqrt n := by
      calc b + 1 = Nat.sqrt ((b + 1) * (b + 1)) := (Nat.sqrt_eq (b + 1)).symm
        _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
    omega
  refine (hbase.comp hmap).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  simp only [Function.comp_apply, fkgq_unitMarg, dif_pos hR]
  rw [ocs_unitEdge_eq_innerEdgeLE d (Nat.sqrt n) hR dir]
  have hrr : 1 + (Nat.sqrt n - 1) = Nat.sqrt n := Nat.add_sub_cancel' hR
  exact congrArg (fun z : {z : ℕ // 1 ≤ z} =>
    edgeMargProb (fkProb (boxGraph d z.1) (fsc_logistic t) q)
      (innerEdgeLE d z.2 (ocs_unitEdge d 1 (le_refl 1) dir)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {z : ℕ // 1 ≤ z})
        = ⟨Nat.sqrt n, hR⟩ from Subtype.ext hrr)


theorem fkgq_unitWiredMarg_tendsto (q : ℝ) (hq : 1 ≤ q) (dir : Fin d × Bool) (t : ℝ) :
    Tendsto (fun n => fkgq_unitWiredMarg d q n dir t) atTop
      (nhds (wiredEdgeDensity d q
        (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t))) := by
  have hbase := fkgq_wired_density_eq_limit (d := d) 1
    (ocs_unitEdge d 1 (le_refl 1) dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  have hmap : Tendsto (fun n : ℕ => Nat.sqrt n - 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + 1) * (b + 1), fun n hn => ?_⟩
    have : b + 1 ≤ Nat.sqrt n := by
      calc b + 1 = Nat.sqrt ((b + 1) * (b + 1)) := (Nat.sqrt_eq (b + 1)).symm
        _ ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hn
    omega
  refine (hbase.comp hmap).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hR : 1 ≤ Nat.sqrt n := by rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]; omega
  simp only [Function.comp_apply, fkgq_unitWiredMarg, dif_pos hR]
  rw [ocs_unitEdge_eq_innerEdgeLE d (Nat.sqrt n) hR dir]
  have hrr : 1 + (Nat.sqrt n - 1) = Nat.sqrt n := Nat.add_sub_cancel' hR
  exact congrArg (fun z : {z : ℕ // 1 ≤ z} =>
    edgeMargProb (wiredFkProb (boxGraph d z.1) (boxBoundary d z.1) (fsc_logistic t) q)
      (innerEdgeLE d z.2 (ocs_unitEdge d 1 (le_refl 1) dir)))
    (show (⟨1 + (Nat.sqrt n - 1), Nat.le_add_right 1 _⟩ : {z : ℕ // 1 ≤ z})
        = ⟨Nat.sqrt n, hR⟩ from Subtype.ext hrr)


noncomputable def fkgq_freeDelta (N : ℕ) (e : Sym2 (boxVerts d N))
    (q t : ℝ) (n : ℕ) : ℝ :=
  ∑ dir : Fin d × Bool,
    |freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) - fkgq_unitMarg d q n dir t|


noncomputable def fkgq_wiredDelta (N : ℕ) (e : Sym2 (boxVerts d N))
    (q t : ℝ) (n : ℕ) : ℝ :=
  ∑ dir : Fin d × Bool,
    |fkgq_unitWiredMarg d q n dir t
      - wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)|

theorem fkgq_freeDelta_nonneg (N : ℕ) (e : Sym2 (boxVerts d N)) (q t : ℝ) (n : ℕ) :
    0 ≤ fkgq_freeDelta N e q t n := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem fkgq_wiredDelta_nonneg (N : ℕ) (e : Sym2 (boxVerts d N)) (q t : ℝ) (n : ℕ) :
    0 ≤ fkgq_wiredDelta N e q t n := Finset.sum_nonneg fun _ _ => abs_nonneg _


theorem fkgq_freeDelta_tendsto_zero (hd : 1 ≤ d) (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∈ (boxGraph d N).edgeFinset) (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => fkgq_freeDelta N e q t n) atTop (nhds 0) := by
  have hdir : ∀ dir : Fin d × Bool,
      freeEdgeDensity d q (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t)
        = freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) := by
    intro dir
    exact (fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) 1 _
      (ocs_unitEdge1_mem_edgeFinset d dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).trans
      (fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
  unfold fkgq_freeDelta
  convert tendsto_finset_sum Finset.univ (fun dir _ =>
    (((tendsto_const_nhds.sub (fkgq_unitMarg_tendsto q hq dir t)).abs).congr'
      (Filter.Eventually.of_forall fun n => rfl))) using 1 <;> simp [hdir]


theorem fkgq_wiredDelta_tendsto_zero (hd : 1 ≤ d) (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∈ (boxGraph d N).edgeFinset) (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => fkgq_wiredDelta N e q t n) atTop (nhds 0) := by
  have hdir : ∀ dir : Fin d × Bool,
      wiredEdgeDensity d q (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t)
        = wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) := by
    intro dir
    exact (fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) 1 _
      (ocs_unitEdge1_mem_edgeFinset d dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).trans
      (fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
  unfold fkgq_wiredDelta
  convert tendsto_finset_sum Finset.univ (fun dir _ =>
    (((fkgq_unitWiredMarg_tendsto q hq dir t).sub tendsto_const_nhds).abs.congr'
      (Filter.Eventually.of_forall fun n => rfl))) using 1 <;> simp [hdir]




theorem fkgq_freeDensity_mem_Icc (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ∈ Set.Icc (0 : ℝ) 1 := by
  have hlim := fkgq_free_density_eq_limit (d := d) N e
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_nonneg (boxGraph d (N + k))
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) (zero_lt_one.trans_le hq)
        (innerEdgeLE d (Nat.le_add_right N k) e))
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_le_one (boxGraph d (N + k))
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) (zero_lt_one.trans_le hq)
        (innerEdgeLE d (Nat.le_add_right N k) e))


theorem fkgq_wiredDensity_mem_Icc (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ∈ Set.Icc (0 : ℝ) 1 := by
  have hlim := fkgq_wired_density_eq_limit (d := d) N e
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (N + k))
        (boxBoundary d (N + k)) (fsc_logistic_pos t) (fsc_logistic_lt_one t)
        (zero_lt_one.trans_le hq) (innerEdgeLE d (Nat.le_add_right N k) e))
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (N + k))
        (boxBoundary d (N + k)) (fsc_logistic_pos t) (fsc_logistic_lt_one t)
        (zero_lt_one.trans_le hq) (innerEdgeLE d (Nat.le_add_right N k) e))

set_option maxHeartbeats 2000000 in

theorem fkgq_free_bulk_lower (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n))
    (hadj : (boxGraph d (n - Nat.sqrt n)).Adj u v) :
    freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) - fkgq_freeDelta N e q t n
      ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n))
          (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n)))) := by
  have hR : 1 ≤ Nat.sqrt n := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]
    omega
  obtain ⟨dir, hdir⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hdir]
    exact ocs_candMap_mem_box d (Nat.sqrt n) hR dir
  have hlow := fkgq_free_offCentre_lower (d := d) (Nat.sqrt n) n
    (Nat.sqrt_le_self n) (Nat.sub_le n (Nat.sqrt n)) u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n)))) =
      ocs_unitEdge d (Nat.sqrt n) hR dir := by
    unfold ocs_unitEdge
    congr 1
    exact Subtype.ext hdir
  rw [hue] at hlow
  have hmarg : fkgq_unitMarg d q n dir t = edgeMargProb
      (fkProb (boxGraph d (Nat.sqrt n)) (fsc_logistic t) q)
      (ocs_unitEdge d (Nat.sqrt n) hR dir) := by
    unfold fkgq_unitMarg
    rw [dif_pos hR]
  have hterm : |freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
      fkgq_unitMarg d q n dir t| ≤ fkgq_freeDelta N e q t n :=
    Finset.single_le_sum (fun x _ => abs_nonneg
      (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
        fkgq_unitMarg d q n x t)) (Finset.mem_univ dir)
  have h1 : freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
      fkgq_freeDelta N e q t n ≤ fkgq_unitMarg d q n dir t := by
    have := (le_abs_self (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
      fkgq_unitMarg d q n dir t)).trans hterm
    linarith
  rw [hmarg] at h1
  exact h1.trans hlow

set_option maxHeartbeats 2000000 in

theorem fkgq_wired_bulk_upper (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n - 1))
    (hadj : (boxGraph d (n - Nat.sqrt n - 1)).Adj u v) :
    edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le (n - Nat.sqrt n) 1 |>.trans
          (Nat.sub_le n (Nat.sqrt n)))
          (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n - 1))))
      ≤ wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) +
        fkgq_wiredDelta N e q t n := by
  have hR : 1 ≤ Nat.sqrt n := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]
    omega
  have hRn1 : Nat.sqrt n + 1 ≤ n := by
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := by
      simpa [pow_two] using Nat.sqrt_le' n
    nlinarith [Nat.sqrt_le_self n, h2]
  let hmn := Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))
  obtain ⟨dir, hdir⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n - 1) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hdir]
    exact ocs_candMap_mem_box d (Nat.sqrt n) hR dir
  have hup := fkgq_wired_offCentre_upper (d := d) (Nat.sqrt n) n hR hRn1 hmn u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n)))) =
      ocs_unitEdge d (Nat.sqrt n) hR dir := by
    unfold ocs_unitEdge
    congr 1
    exact Subtype.ext hdir
  rw [hue] at hup
  have hmarg : fkgq_unitWiredMarg d q n dir t = edgeMargProb
      (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n))
        (fsc_logistic t) q) (ocs_unitEdge d (Nat.sqrt n) hR dir) := by
    unfold fkgq_unitWiredMarg
    rw [dif_pos hR]
  have hterm : |fkgq_unitWiredMarg d q n dir t -
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)| ≤
      fkgq_wiredDelta N e q t n :=
    Finset.single_le_sum (fun x _ => abs_nonneg
      (fkgq_unitWiredMarg d q n x t -
        wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)))
      (Finset.mem_univ dir)
  have h1 : fkgq_unitWiredMarg d q n dir t ≤
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) +
        fkgq_wiredDelta N e q t n := by
    have := (le_abs_self (fkgq_unitWiredMarg d q n dir t -
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))).trans hterm
    linarith
  rw [hmarg] at h1
  exact hup.trans h1


theorem fkgq_genuineFreeCollapse (hd : 1 ≤ d) (N : ℕ)
    (e : Sym2 (boxVerts d N)) (he : e ∈ (boxGraph d N).edgeFinset)
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop
      (nhds (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) := by
  let L := freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)
  obtain ⟨hL0, hL1⟩ := fkgq_freeDensity_mem_Icc N e q hq t
  let In := ocs_bulkSet d
  let δ := fkgq_freeDelta N e q t
  apply fkgq_freeBulkCollapse_n1 q t (zero_lt_one.trans_le hq)
    (fun n hn => ecz_box_edge_pos d hd hn) L hL0 hL1 In
  · intro n x hx
    change x ∈ ocs_bulkSet d n at hx
    rw [ocs_bulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => fkgq_freeDelta_nonneg N e q t n
  · exact fkgq_freeDelta_tendsto_zero hd N e he q hq t
  · intro n x hx
    change x ∈ ocs_bulkSet d n at hx
    rw [ocs_bulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    rw [SimpleGraph.mem_edgeFinset] at heb
    have hupper : edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)) eb) ≤ L := by
      refine (fkgq_free_per_edge_upper n _ (fsc_logistic_pos t)
        (fsc_logistic_lt_one t) hq).trans_eq ?_
      rw [edgeIncl_innerEdgeLE]
      calc
        freeEdgeDensity d q (edgeIncl d (n - Nat.sqrt n) eb) (fsc_logistic t)
            = freeEdgeDensity d q (rot_refUnitEdge d (lt_of_lt_of_le one_pos hd))
                (fsc_logistic t) :=
          fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) _ eb
            (by simpa [SimpleGraph.mem_edgeFinset] using heb)
            (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
        _ = L := by
          dsimp [L]
          exact (fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
            (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
    have hlower : L - δ n ≤ edgeMargProb
        (fkProb (boxGraph d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)) eb) := by
      by_cases hn : 1 ≤ n
      · induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          exact fkgq_free_bulk_lower N e q hq t n hn u v heb
      · exfalso
        have hn0 : n = 0 := by omega
        subst n
        induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          have huv : (u : Site d) = (v : Site d) := by
            funext i
            have hu := u.2 i
            have hv := v.2 i
            simp only [Nat.zero_sub, mem_box] at hu hv
            omega
          rw [boxGraph, SimpleGraph.comap_adj, huv] at heb
          simpa [NearestNeighbour] using heb
    rw [abs_le]
    constructor <;> linarith [fkgq_freeDelta_nonneg N e q t n]
  · have hcard : ∀ n, (In n).card =
        (boxGraph d (n - Nat.sqrt n)).edgeFinset.card := fun n =>
      Finset.card_image_of_injective _
        (dfi_innerEdgeLE_injective d (Nat.sub_le n (Nat.sqrt n)))
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd
      (fun n => n - Nat.sqrt n) (fun n => Nat.sub_le n _)
      ocs_gap_sub_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]


theorem fkgq_genuineWiredCollapse (hd : 1 ≤ d) (N : ℕ)
    (e : Sym2 (boxVerts d N)) (he : e ∈ (boxGraph d N).edgeFinset)
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) atTop
      (nhds (wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) := by
  let L := wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)
  obtain ⟨hL0, hL1⟩ := fkgq_wiredDensity_mem_Icc N e q hq t
  let In := ocs_wiredBulkSet d
  let δ := fkgq_wiredDelta N e q t
  apply fkgq_wiredBulkCollapse_n1 q t (zero_lt_one.trans_le hq)
    (fun n hn => ecz_box_edge_pos d hd hn) L hL0 hL1 In
  · intro n x hx
    change x ∈ ocs_wiredBulkSet d n at hx
    rw [ocs_wiredBulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => fkgq_wiredDelta_nonneg N e q t n
  · exact fkgq_wiredDelta_tendsto_zero hd N e he q hq t
  · intro n x hx
    change x ∈ ocs_wiredBulkSet d n at hx
    rw [ocs_wiredBulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    rw [SimpleGraph.mem_edgeFinset] at heb
    let hmn := Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))
    have hlower : L ≤ edgeMargProb
        (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q)
        (innerEdgeLE d hmn eb) := by
      have hconst : L = wiredEdgeDensity d q (edgeIncl d (n - Nat.sqrt n - 1) eb)
          (fsc_logistic t) := by
        dsimp [L]
        calc
          wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)
              = wiredEdgeDensity d q (rot_refUnitEdge d (lt_of_lt_of_le one_pos hd))
                  (fsc_logistic t) :=
            fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
              (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
          _ = wiredEdgeDensity d q (edgeIncl d (n - Nat.sqrt n - 1) eb)
                (fsc_logistic t) :=
            (fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) _ eb
              (by simpa [SimpleGraph.mem_edgeFinset] using heb)
              (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
      rw [hconst]
      rw [← edgeIncl_innerEdgeLE]
      exact fkgq_wired_per_edge_lower n _ (fsc_logistic_pos t)
        (fsc_logistic_lt_one t) hq
    have hupper : edgeMargProb
        (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q)
        (innerEdgeLE d hmn eb) ≤ L + δ n := by
      by_cases hn : 2 ≤ n
      · induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          exact fkgq_wired_bulk_upper N e q hq t n hn u v heb
      · exfalso
        have hzero : n - Nat.sqrt n - 1 = 0 := by
          interval_cases n <;> simp [Nat.sqrt]
        induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          have huv : (u : Site d) = (v : Site d) := by
            funext i
            have hu := u.2 i
            have hv := v.2 i
            simp only [mem_box, hzero] at hu hv
            omega
          rw [boxGraph, SimpleGraph.comap_adj, huv] at heb
          simpa [NearestNeighbour] using heb
    rw [abs_le]
    constructor <;> linarith [fkgq_wiredDelta_nonneg N e q t n]
  · have hcard : ∀ n, (In n).card =
        (boxGraph d (n - Nat.sqrt n - 1)).edgeFinset.card := fun n =>
      Finset.card_image_of_injective _ (dfi_innerEdgeLE_injective d _)
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd
      (fun n => n - Nat.sqrt n - 1)
      (fun n => Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n)))
      ocs_gap_sub_one_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]




theorem fkgq_free_density_nonEdge (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∉ (boxGraph d N).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N e) p = 1 / 2 := by
  have hlim := fkgq_free_density_eq_limit (d := d) N e hp hp1 hq
  have hconst : (fun k => edgeMargProb (fkProb (boxGraph d (N + k)) p q)
      (innerEdgeLE d (Nat.le_add_right N k) e)) = fun _ => (1 / 2 : ℝ) := by
    funext k
    apply fpe2_edgeMargProb_half_of_toggle_invariant
    · exact fkProb_sum_eq_one (boxGraph d (N + k)) hp hp1 (zero_lt_one.trans_le hq)
    · intro ω
      exact fpe2_fkProb_toggle_invariant (boxGraph d (N + k))
        (fpe2_innerEdgeLE_notMem_edgeFinset N (N + k) (Nat.le_add_right N k) e he) ω
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm


theorem fkgq_wired_density_nonEdge (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∉ (boxGraph d N).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d N e) p = 1 / 2 := by
  have hlim := fkgq_wired_density_eq_limit (d := d) N e hp hp1 hq
  have hconst : (fun k => edgeMargProb
      (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p q)
      (innerEdgeLE d (Nat.le_add_right N k) e)) = fun _ => (1 / 2 : ℝ) := by
    funext k
    apply fpe2_edgeMargProb_half_of_toggle_invariant
    · exact wiredFkProb_sum_eq_one (boxGraph d (N + k)) (boxBoundary d (N + k))
        hp hp1 (zero_lt_one.trans_le hq)
    · intro ω
      exact fpe2_wiredFkProb_toggle_invariant (boxGraph d (N + k))
        (boxBoundary d (N + k))
        (fpe2_innerEdgeLE_notMem_edgeFinset N (N + k) (Nat.le_add_right N k) e he) ω
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm


theorem fkgq_free_density_le_wired (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N e) p ≤
      wiredEdgeDensity d q (edgeIncl d N e) p := by
  have h := fkgq_freeIV_le_wiredIV d N hp hp1 hq
    (boxEdgeOpenEvent_isIncreasing d N e)
  unfold freeEdgeDensity wiredEdgeDensity
  rw [dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩,
    dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩]
  exact h



theorem fkgq_centered_deriv_eq_densities (hd : 1 ≤ d) (q : ℝ) (hq : 1 ≤ q)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ Set.univ G)
    (hlim : ∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s)))
    (N : ℕ) (e : Sym2 (boxVerts d N)) (he : e ∈ (boxGraph d N).edgeFinset)
    (t : ℝ) (hdiff : pressureLeftDeriv G t = pressureRightDeriv G t) :
    freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) = pressureLeftDeriv G t ∧
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) = pressureRightDeriv G t := by
  have hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card :=
    fun n hn => ecz_box_edge_pos d hd hn
  have hshift : ∀ s, Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) q s)
      atTop (nhds (G s)) := fun s => (hlim s).comp (tendsto_add_atTop_nat 1)
  have hfreeCol : Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop
      (nhds (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) :=
    fkgq_genuineFreeCollapse hd N e he q hq t
  have hwiredCol : Tendsto
      (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) atTop
      (nhds (wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) :=
    fkgq_genuineWiredCollapse hd N e he q hq t
  have hfreeShift := hfreeCol.comp (tendsto_add_atTop_nat 1)
  have hwiredShift := hwiredCol.comp (tendsto_add_atTop_nat 1)
  have hfreeL : pressureLeftDeriv G t ≤
      freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) :=
    fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d (n + 1)) q) G
      (fun n => fkgq_avgDensity (boxGraph d (n + 1)) q)
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)))
      (fun n s => fkgq_centered_hasDerivAt (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)) s)
      hshift t _ hG hfreeShift
  have hfreeR : freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ≤
      pressureRightDeriv G t :=
    fdd_avgLimit_le_rightDeriv
      (fun n => cfe_centered (boxGraph d (n + 1)) q) G
      (fun n => fkgq_avgDensity (boxGraph d (n + 1)) q)
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)))
      (fun n s => fkgq_centered_hasDerivAt (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)) s)
      hshift t _ hG hfreeShift
  have hwlim : ∀ s, Tendsto (fun n => cfe_wiredCentered (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) q s) atTop (nhds (G s)) := fun s =>
    (fkgq_wiredCentered_tendsto d hd q hq s (hlim s)).comp (tendsto_add_atTop_nat 1)
  have hwiredR : wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ≤
      pressureRightDeriv G t :=
    fdd_avgLimit_le_rightDeriv
      (fun n => cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q) G
      (fun n => wpd_avgWiredDensity (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q)
      (fun n => cfe_wiredCentered_convexOn (boxGraph d (n + 1))
        (boxBoundary d (n + 1)) q (zero_lt_one.trans_le hq)
        (hbox1 (n + 1) (by omega)))
      (fun n s => fkgq_wiredCentered_hasDerivAt (boxGraph d (n + 1))
        (boxBoundary d (n + 1)) q (zero_lt_one.trans_le hq)
        (hbox1 (n + 1) (by omega)) s)
      hwlim t _ hG hwiredShift
  have hfw := fkgq_free_density_le_wired N e
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  constructor
  · apply le_antisymm
    · exact hfreeR.trans_eq hdiff.symm
    · exact hfreeL
  · apply le_antisymm hwiredR
    rw [← hdiff]
    exact hfreeL.trans hfw



theorem fkgq_countable_free_wired_disagreement (hd : 1 ≤ d) (N : ℕ)
    (q : ℝ) (hq : 1 ≤ q) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
      eventMassProb (fkgq_freeMass d N q hq t) A ≠
        eventMassProb (fkgq_wiredMass d N q hq t) A}.Countable := by
  obtain ⟨G, hlim, hG, _⟩ := fkgq_centeredConvergence d hd q hq
  refine (countable_leftDeriv_ne_rightDeriv hG).mono ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  by_contra hdiff
  obtain ⟨A, hA, hne⟩ := ht
  obtain ⟨P, hP⟩ := fkgq_hcoup d N q hq t
  apply hne
  refine fk_unique_of_edgeMarg_eq hP ?_ hA
  intro e
  rw [fkgq_edgeMarg_free, fkgq_edgeMarg_wired]
  by_cases he : e ∈ (boxGraph d N).edgeFinset
  · obtain ⟨hf, hw⟩ :=
      fkgq_centered_deriv_eq_densities hd q hq hG hlim N e he t hdiff
    rw [hf, hw, hdiff]
  · rw [fkgq_free_density_nonEdge N e he (fsc_logistic_pos t)
      (fsc_logistic_lt_one t) hq,
      fkgq_wired_density_nonEdge N e he (fsc_logistic_pos t)
      (fsc_logistic_lt_one t) hq]

end StatMech.FK
