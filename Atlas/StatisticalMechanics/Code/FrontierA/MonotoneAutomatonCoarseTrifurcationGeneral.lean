/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.AllOpenCoarseProbabilityGeneral
import Code.FrontierA.MonotoneAutomatonFiniteMerge
import Code.Walls.bc117mergeproof

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open StatMech.Walls

variable {d : ℕ}





theorem removeBox_siteForce_eq_general (d n : ℕ)
    (eta : ConfigSpace (Site d)) :
    removeSites (bc61_boxAround d n 0)
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) =
      removeSites (bc61_boxAround d n 0) (siteToBond eta) := by
  classical
  rw [bc61_boxAround_zero]
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      unfold removeSites
      by_cases hinc : ∃ t ∈ boxFinsetBK d n, t ∈ s(x, y)
      · rw [if_pos hinc, if_pos hinc]
      · rw [if_neg hinc, if_neg hinc]
        have hx : x ∉ boxFinsetBK d n := by
          intro hx
          exact hinc ⟨x, hx, by simp⟩
        have hy : y ∉ boxFinsetBK d n := by
          intro hy
          exact hinc ⟨y, hy, by simp⟩
        simp [siteToBond_mk, forceSitesOccupied_apply, hx, hy]


theorem siteToBond_le_siteForce_general (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    siteToBond eta ≤
      siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) := by
  apply siteToBond_mono
  intro x
  by_cases hx : x ∈ boxFinsetBK d n <;>
    simp [forceSitesOccupied_apply, hx]



theorem siteForce_bgfdIndexAllOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    BgfdIndexAllOpen
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
  intro x y hx hy _hadj
  have hxbox : x ∈ box d n := by
    have h := bgfd_idx_iff_inBox.mp hx
    rw [bgfd_centre_zero] at h
    simpa [bgfdInBox] using h
  have hybox : y ∈ box d n := by
    have h := bgfd_idx_iff_inBox.mp hy
    rw [bgfd_centre_zero] at h
    simpa [bgfdInBox] using h
  simp [siteToBond_mk, forceSitesOccupied_apply,
    mem_boxFinsetBK_iff.mpr hxbox, mem_boxFinsetBK_iff.mpr hybox]



theorem coarseTrif_siteForce_of_coarse_general (n : ℕ)
    (eta : ConfigSpace (Site d))
    (h : bc61_IsCoarseTrifurcation (siteToBond eta) n 0) :
    bc61_IsCoarseTrifurcation
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
  obtain ⟨a₁, a₂, a₃, hi₁, hi₂, hi₃, hinf, hcut⟩ := h
  have hmono := siteToBond_le_siteForce_general n eta
  refine ⟨a₁, a₂, a₃, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hba⟩ := hi₁
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₂
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₃
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · simpa only [removeBox_siteForce_eq_general] using hinf
  · simpa only [removeBox_siteForce_eq_general] using hcut





theorem shell_of_walk_into_box_general {L : ℕ}
    {omega : ConfigSpace (Sym2 (Site d))} {b u x : Site d}
    (w : (openSubgraph d omega).Walk u x) :
    Connected d (removeSites (bc61_boxAround d L 0) omega) b u →
      u ∉ bc61_boxAround d L 0 → x ∈ bc61_boxAround d L 0 →
      ∃ s t : Site d, (openSubgraph d omega).Adj s t ∧
        t ∈ bc61_boxAround d L 0 ∧
        Connected d (removeSites (bc61_boxAround d L 0) omega) b s := by
  induction w with
  | nil =>
      intro _ hu hx
      exact absurd hx hu
  | @cons u v z hadj w' ih =>
      intro hbu hu hx
      by_cases hv : v ∈ bc61_boxAround d L 0
      · exact ⟨u, v, hadj, hv, hbu⟩
      · have hstep : Connected d
            (removeSites (bc61_boxAround d L 0) omega) u v :=
          bc117_cut_step_of_notMem hadj hu hv
        exact ih (hbu.trans hstep) hv hx



theorem attach_of_meetsBox_general {L : ℕ}
    {omega : ConfigSpace (Sym2 (Site d))} {x x' : Site d}
    (hinf : (cluster d omega x).Infinite)
    (hx'box : x' ∈ bc61_boxAround d L 0)
    (hxx' : cluster d omega x = cluster d omega x') :
    ∃ a : Site d,
      (∃ bx ∈ bc61_boxAround d L 0, (openSubgraph d omega).Adj bx a) ∧
      (cluster d (removeSites (bc61_boxAround d L 0) omega) a).Infinite ∧
      cluster d omega x = cluster d omega a := by
  classical
  obtain ⟨b, hbconn, hbnot, hbinf⟩ :=
    bc117_boxAvoiding_external_infinite omega hinf (bc61_boxAround d L 0)
  have hxx'conn : Connected d omega x x' := by
    have hx'mem : x' ∈ cluster d omega x := by
      rw [hxx']
      exact self_mem_cluster omega x'
    exact mem_cluster.mp hx'mem
  have hbx' : Connected d omega b x' := hbconn.symm.trans hxx'conn
  obtain ⟨w⟩ := hbx'
  obtain ⟨s, t, hadj, htbox, hscut⟩ :=
    shell_of_walk_into_box_general (b := b) w
      (connected_refl _ b) hbnot hx'box
  refine ⟨s, ⟨t, htbox, hadj.symm⟩, ?_, ?_⟩
  · have hcl : cluster d (removeSites (bc61_boxAround d L 0) omega) b =
        cluster d (removeSites (bc61_boxAround d L 0) omega) s :=
      cluster_eq_of_connected hscut
    rwa [hcl] at hbinf
  · have hbs : Connected d omega b s := bc61_connected_of_cut hscut
    exact cluster_eq_of_connected (hbconn.trans hbs)



theorem coarseTrif_of_three_meetBox_general {L : ℕ}
    {omega : ConfigSpace (Sym2 (Site d))} {x₁ x₂ x₃ : Site d}
    (hi₁ : (cluster d omega x₁).Infinite)
    (hi₂ : (cluster d omega x₂).Infinite)
    (hi₃ : (cluster d omega x₃).Infinite)
    (hd₁₂ : cluster d omega x₁ ≠ cluster d omega x₂)
    (hd₁₃ : cluster d omega x₁ ≠ cluster d omega x₃)
    (hd₂₃ : cluster d omega x₂ ≠ cluster d omega x₃)
    (hb₁ : x₁ ∈ bc61_boxAround d L 0)
    (hb₂ : x₂ ∈ bc61_boxAround d L 0)
    (hb₃ : x₃ ∈ bc61_boxAround d L 0) :
    bc61_IsCoarseTrifurcation omega L 0 := by
  obtain ⟨a₁, hadj₁, hinf₁, he₁⟩ :=
    attach_of_meetsBox_general hi₁ hb₁ rfl
  obtain ⟨a₂, hadj₂, hinf₂, he₂⟩ :=
    attach_of_meetsBox_general hi₂ hb₂ rfl
  obtain ⟨a₃, hadj₃, hinf₃, he₃⟩ :=
    attach_of_meetsBox_general hi₃ hb₃ rfl
  have hda₁₂ : cluster d omega a₁ ≠ cluster d omega a₂ := by
    rw [← he₁, ← he₂]
    exact hd₁₂
  have hda₁₃ : cluster d omega a₁ ≠ cluster d omega a₃ := by
    rw [← he₁, ← he₃]
    exact hd₁₃
  have hda₂₃ : cluster d omega a₂ ≠ cluster d omega a₃ := by
    rw [← he₂, ← he₃]
    exact hd₂₃
  exact ⟨a₁, a₂, a₃, hadj₁, hadj₂, hadj₃,
    ⟨hinf₁, hinf₂, hinf₃⟩,
    bc115_disconnected_of_distinctClusters _ omega hda₁₂,
    bc115_disconnected_of_distinctClusters _ omega hda₁₃,
    bc115_disconnected_of_distinctClusters _ omega hda₂₃⟩



theorem siteForce_bgfdFaithfulAllOpenTrif_of_threeMeetBox
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (h : siteToBond eta ∈ threeMeetBox d n) :
    BgfdFaithfulAllOpenTrifAt
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
  obtain ⟨_htop, x₁, x₂, x₃, hb₁, hb₂, hb₃,
    hi₁, hi₂, hi₃, hd₁₂, hd₁₃, hd₂₃⟩ := h
  have hb₁' : x₁ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₁
  have hb₂' : x₂ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₂
  have hb₃' : x₃ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₃
  have hcoarse : bc61_IsCoarseTrifurcation (siteToBond eta) n 0 :=
    coarseTrif_of_three_meetBox_general hi₁ hi₂ hi₃
      hd₁₂ hd₁₃ hd₂₃ hb₁' hb₂' hb₃'
  refine ⟨?_, siteForce_bgfdIndexAllOpen n eta⟩
  rw [bgfd_centre_zero]
  exact (bc67_coarseTrif_is_G_n_trifurcation _ n 0).mp
    (coarseTrif_siteForce_of_coarse_general n eta hcoarse)





def SiteBgfdFaithfulAllOpenTrifAt (d n : ℕ) :
    Set (ConfigSpace (Site d)) :=
  siteToBond ⁻¹' {omega | BgfdFaithfulAllOpenTrifAt omega n 0}

theorem measurableSet_siteBgfdFaithfulAllOpenTrifAt (d n : ℕ) :
    MeasurableSet (SiteBgfdFaithfulAllOpenTrifAt d n) :=
  measurable_siteToBond (measurableSet_bgfdFaithfulAllOpenTrifAt n 0)


def SiteThreeMeetBoxGeneral (d n : ℕ) : Set (ConfigSpace (Site d)) :=
  siteToBond ⁻¹' threeMeetBox d n



theorem exists_siteThreeMeetBox_pos_general
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (htop : 0 < nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤}) :
    ∃ n : ℕ, 0 < nu (SiteThreeMeetBoxGeneral d n) := by
  have hcover : {eta : ConfigSpace (Site d) |
      numInfiniteClusters d (siteToBond eta) = ⊤} ⊆
      ⋃ n, SiteThreeMeetBoxGeneral d n := by
    intro eta heta
    have hmem := iEqTop_subset_iUnion_threeMeetBox (d := d) heta
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : nu (⋃ n, SiteThreeMeetBoxGeneral d n) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      nu (⋃ n, SiteThreeMeetBoxGeneral d n) ≤
          ∑' n, nu (SiteThreeMeetBoxGeneral d n) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle :
      nu {eta : ConfigSpace (Site d) |
          numInfiniteClusters d (siteToBond eta) = ⊤} ≤
        nu (⋃ n, SiteThreeMeetBoxGeneral d n) :=
    measure_mono hcover
  rw [hunion0] at hle
  exact (not_lt_of_ge hle) htop



theorem siteBgfdFaithfulAllOpenTrif_pos_of_top
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (htop : 0 < nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤}) :
    ∃ n : ℕ, 0 < nu (SiteBgfdFaithfulAllOpenTrifAt d n) := by
  obtain ⟨n, hnpos⟩ := exists_siteThreeMeetBox_pos_general nu htop
  refine ⟨n, positive_of_forceSitesOccupied_preimage
    nu epsilon hepsilon hinsert (boxFinsetBK d n)
      (measurableSet_siteBgfdFaithfulAllOpenTrifAt d n) ?_ hnpos⟩
  intro eta heta
  exact siteForce_bgfdFaithfulAllOpenTrif_of_threeMeetBox eta n heta



theorem siteBgfdFaithfulAllOpenTrif_prob_eq_zero
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
    (n : ℕ) :
    nu (SiteBgfdFaithfulAllOpenTrifAt d n) = 0 := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) := Measure.map siteToBond nu
  haveI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map measurable_siteToBond.aemeasurable
  have hmuv : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    siteToBond_isTranslationInvariant nu hinv
  have hzero := bgfdFaithfulAllOpenTrifAt_prob_eq_zero mu hd hmuv n
  rw [Measure.map_apply measurable_siteToBond
    (measurableSet_bgfdFaithfulAllOpenTrifAt n 0)] at hzero
  exact hzero



theorem site_cluster_count_top_null_general
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤} = 0 := by
  by_contra hne
  have hpos : 0 < nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤} :=
    pos_iff_ne_zero.mpr hne
  obtain ⟨n, hnpos⟩ := siteBgfdFaithfulAllOpenTrif_pos_of_top
    nu epsilon hepsilon hinsert hpos
  rw [siteBgfdFaithfulAllOpenTrif_prob_eq_zero nu hd hinv n] at hnpos
  exact (lt_irrefl 0) hnpos





theorem site_cluster_count_ae_one_general
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (hperco : nu {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1) :
    nu {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
  rcases site_cluster_count_ae_one_or_infinite
      nu herg epsilon hepsilon hinsert hperco with hone | htop
  · exact hone
  · rw [site_cluster_count_top_null_general
      nu hd herg.1 epsilon hepsilon hinsert] at htop
    exact False.elim (zero_ne_one htop)



theorem site_cluster_count_ae_zero_or_one_general
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    nu {eta | numInfiniteClusters d (siteToBond eta) = 0} = 1 ∨
      nu {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
  obtain ⟨k, hk, hkCases⟩ := site_cluster_count_ae_lt_two_or_infinite
    nu herg epsilon hepsilon hinsert
  rcases hkCases with hk2 | hktop
  · have hkle : k ≤ 1 := enat_le_one_of_not_two hk2
    by_cases hkzero : k = 0
    · left
      rwa [hkzero] at hk
    · have hkone : k = 1 :=
        le_antisymm hkle (ENat.one_le_iff_ne_zero.mpr hkzero)
      right
      rwa [hkone] at hk
  · have htopzero := site_cluster_count_top_null_general
      nu hd herg.1 epsilon hepsilon hinsert
    rw [hktop, htopzero] at hk
    exact False.elim (zero_ne_one hk)



theorem interpolatedSite_cluster_count_ae_zero_or_one_general
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
    (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters d (siteToBond eta) = 0} = 1 ∨
      (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
  letI : IsProbabilityMeasure (interpolatedSiteLaw T mu) := by
    unfold interpolatedSiteLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_interpolatedSite T).aemeasurable
  exact site_cluster_count_ae_zero_or_one_general
    (interpolatedSiteLaw T mu) hd
    (interpolatedSiteLaw_isErgodic T mu herg)
    epsilon hepsilon
    (interpolatedSiteLaw_hasInsertionLowerBound T mu epsilon hinsert)

end StatMech.FrontierA
