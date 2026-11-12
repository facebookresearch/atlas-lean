/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.AllOpenCoarseProbability
import Code.FrontierA.MonotoneAutomatonFiniteMerge
import Code.Walls.bkmmerge

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open StatMech.Walls


theorem removeBox_siteForce_eq (n : ℕ) (eta : ConfigSpace (Site 2)) :
    removeSites (bc61_boxAround 2 n 0)
        (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) =
      removeSites (bc61_boxAround 2 n 0) (siteToBond eta) := by
  classical
  rw [bc61_boxAround_zero]
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      unfold removeSites
      by_cases hinc : ∃ t ∈ boxFinsetBK 2 n, t ∈ s(x, y)
      · rw [if_pos hinc, if_pos hinc]
      · rw [if_neg hinc, if_neg hinc]
        have hx : x ∉ boxFinsetBK 2 n := by
          intro hx
          exact hinc ⟨x, hx, by simp⟩
        have hy : y ∉ boxFinsetBK 2 n := by
          intro hy
          exact hinc ⟨y, hy, by simp⟩
        simp [siteToBond_mk, forceSitesOccupied_apply, hx, hy]


theorem siteToBond_le_siteForce (n : ℕ) (eta : ConfigSpace (Site 2)) :
    siteToBond eta ≤
      siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta) := by
  apply siteToBond_mono
  intro x
  by_cases hx : x ∈ boxFinsetBK 2 n <;>
    simp [forceSitesOccupied_apply, hx]


theorem siteForce_box_allOpen (n : ℕ) (eta : ConfigSpace (Site 2)) :
    bff_BoxAllOpen
      (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      obtain ⟨hx, hy, _hadj⟩ := mem_boxEdges_iff.mp he
      simp [siteToBond_mk, forceSitesOccupied_apply,
        mem_boxFinsetBK_iff.mpr hx, mem_boxFinsetBK_iff.mpr hy]



theorem coarseTrif_siteForce_of_coarse (n : ℕ)
    (eta : ConfigSpace (Site 2))
    (h : bc61_IsCoarseTrifurcation (siteToBond eta) n 0) :
    bc61_IsCoarseTrifurcation
      (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n 0 := by
  obtain ⟨a₁, a₂, a₃, hi₁, hi₂, hi₃, hinf, hcut⟩ := h
  have hmono := siteToBond_le_siteForce n eta
  refine ⟨a₁, a₂, a₃, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hba⟩ := hi₁
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₂
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₃
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · simpa only [removeBox_siteForce_eq] using hinf
  · simpa only [removeBox_siteForce_eq] using hcut



theorem siteForce_faithfulAllOpenTrif_of_threeMeetBox
    (eta : ConfigSpace (Site 2)) (n : ℕ)
    (h : siteToBond eta ∈ threeMeetBox 2 n) :
    FaithfulAllOpenTrifAt
      (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n 0 := by
  obtain ⟨_htop, x₁, x₂, x₃, hb₁, hb₂, hb₃,
    hi₁, hi₂, hi₃, hd₁₂, hd₁₃, hd₂₃⟩ := h
  have hcoarse : bc61_IsCoarseTrifurcation (siteToBond eta) n 0 :=
    bkm_coarseTrif_of_le (le_refl n) hb₁ hb₂ hb₃
      hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  refine ⟨?_, bgf2_indexAllOpen_zero_of_bff (siteForce_box_allOpen n eta)⟩
  rw [bgf2_centre_zero]
  exact (bc67_coarseTrif_is_G_n_trifurcation _ n 0).mp
    (coarseTrif_siteForce_of_coarse n eta hcoarse)


def SiteFaithfulAllOpenTrifAt (n : ℕ) : Set (ConfigSpace (Site 2)) :=
  siteToBond ⁻¹' {omega | FaithfulAllOpenTrifAt omega n 0}

theorem measurableSet_siteFaithfulAllOpenTrifAt (n : ℕ) :
    MeasurableSet (SiteFaithfulAllOpenTrifAt n) :=
  measurable_siteToBond (measurableSet_faithfulAllOpenTrifAt n 0)


def SiteThreeMeetBox (n : ℕ) : Set (ConfigSpace (Site 2)) :=
  siteToBond ⁻¹' threeMeetBox 2 n



theorem exists_siteThreeMeetBox_pos
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (htop : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤}) :
    ∃ n : ℕ, 0 < nu (SiteThreeMeetBox n) := by
  have hcover : {eta : ConfigSpace (Site 2) |
      numInfiniteClusters 2 (siteToBond eta) = ⊤} ⊆
      ⋃ n, SiteThreeMeetBox n := by
    intro eta heta
    have hmem := iEqTop_subset_iUnion_threeMeetBox (d := 2) heta
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : nu (⋃ n, SiteThreeMeetBox n) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      nu (⋃ n, SiteThreeMeetBox n) ≤
          ∑' n, nu (SiteThreeMeetBox n) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle :
      nu {eta : ConfigSpace (Site 2) |
          numInfiniteClusters 2 (siteToBond eta) = ⊤} ≤
        nu (⋃ n, SiteThreeMeetBox n) :=
    measure_mono hcover
  rw [hunion0] at hle
  exact (not_lt_of_ge hle) htop



theorem siteFaithfulAllOpenTrif_pos_of_top
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (htop : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤}) :
    ∃ n : ℕ, 0 < nu (SiteFaithfulAllOpenTrifAt n) := by
  obtain ⟨n, hnpos⟩ := exists_siteThreeMeetBox_pos nu htop
  refine ⟨n, positive_of_forceSitesOccupied_preimage
    nu epsilon hepsilon hinsert (boxFinsetBK 2 n)
      (measurableSet_siteFaithfulAllOpenTrifAt n) ?_ hnpos⟩
  intro eta heta
  exact siteForce_faithfulAllOpenTrif_of_threeMeetBox eta n heta



theorem siteFaithfulAllOpenTrif_prob_eq_zero
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) nu)
    (n : ℕ) :
    nu (SiteFaithfulAllOpenTrifAt n) = 0 := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) := Measure.map siteToBond nu
  haveI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map measurable_siteToBond.aemeasurable
  have hmuv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu :=
    siteToBond_isTranslationInvariant nu hinv
  have hzero := faithfulAllOpenTrifAt_prob_eq_zero mu hmuv n
  rw [Measure.map_apply measurable_siteToBond
    (measurableSet_faithfulAllOpenTrifAt n 0)] at hzero
  exact hzero



theorem site_cluster_count_top_null_two
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤} = 0 := by
  by_contra hne
  have hpos : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤} :=
    pos_iff_ne_zero.mpr hne
  obtain ⟨n, hnpos⟩ := siteFaithfulAllOpenTrif_pos_of_top
    nu epsilon hepsilon hinsert hpos
  rw [siteFaithfulAllOpenTrif_prob_eq_zero nu hinv n] at hnpos
  exact (lt_irrefl 0) hnpos



theorem site_cluster_count_ae_one_two
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site 2)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (hperco : nu {eta | 1 ≤ numInfiniteClusters 2 (siteToBond eta)} = 1) :
    nu {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
  rcases site_cluster_count_ae_one_or_infinite
      nu herg epsilon hepsilon hinsert hperco with hone | htop
  · exact hone
  · rw [site_cluster_count_top_null_two nu herg.1 epsilon hepsilon hinsert] at htop
    exact False.elim (zero_ne_one htop)




theorem site_cluster_count_ae_zero_or_one_two
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site 2)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    nu {eta | numInfiniteClusters 2 (siteToBond eta) = 0} = 1 ∨
      nu {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
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
  · have htopzero := site_cluster_count_top_null_two
      nu herg.1 epsilon hepsilon hinsert
    rw [hktop, htopzero] at hk
    exact False.elim (zero_ne_one hk)



theorem interpolatedSite_cluster_count_ae_zero_or_one_two
    (T : MonotoneAutomaton 2) (mu : Measure (FieldTriple 2))
    [IsProbabilityMeasure mu]
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
    (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters 2 (siteToBond eta) = 0} = 1 ∨
      (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
  letI : IsProbabilityMeasure (interpolatedSiteLaw T mu) := by
    unfold interpolatedSiteLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_interpolatedSite T).aemeasurable
  exact site_cluster_count_ae_zero_or_one_two
    (interpolatedSiteLaw T mu)
    (interpolatedSiteLaw_isErgodic T mu herg)
    epsilon hepsilon
    (interpolatedSiteLaw_hasInsertionLowerBound T mu epsilon hinsert)

end StatMech.FrontierA
