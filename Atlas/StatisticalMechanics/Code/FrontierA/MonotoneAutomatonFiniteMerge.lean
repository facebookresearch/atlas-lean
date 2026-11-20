/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.FrontierA.MonotoneAutomatonInsertion
import Code.Percolation.BurtonKeaneMergeGeom
import Code.Percolation.OffClusterIndep

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}



noncomputable def siteForceEdges (n : ℕ) (eta : ConfigSpace (Site d)) :
    Finset (Sym2 (Site d)) :=
  (boxEdges d (n + 1)).filter fun e =>
    siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) e = true



theorem mem_boxFinsetBK_iff {n : ℕ} {x : Site d} :
    x ∈ boxFinsetBK d n ↔ x ∈ box d n := by
  simp [boxFinsetBK]


theorem box_subset_box_succ (n : ℕ) : box d n ⊆ box d (n + 1) := by
  intro x hx i
  exact le_trans (hx i) (Nat.le_succ n)



theorem mem_box_of_forceSitesOccupied_true_of_false (n : ℕ)
    (eta : ConfigSpace (Site d)) (x : Site d)
    (hforced : forceSitesOccupied (boxFinsetBK d n) eta x = true)
    (hclosed : eta x = false) : x ∈ box d n := by
  by_contra hx
  have hx' : x ∉ boxFinsetBK d n := by
    simpa [mem_boxFinsetBK_iff] using hx
  rw [forceSitesOccupied_apply, if_neg hx', hclosed] at hforced
  contradiction





theorem openSubgraph_siteForce_eq_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    openSubgraph d
        (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) =
      openSubgraph d
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    by_cases hmem : s(x, y) ∈ siteForceEdges n eta
    · have hnew :
          siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) s(x, y) = true := by
        simpa [siteForceEdges] using (Finset.mem_filter.mp hmem).2
      exact hnew
    · rw [forceOpenFinset_of_notMem hmem] at hopen
      have hmono : siteToBond eta ≤
          siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) := by
        apply siteToBond_mono
        intro z
        by_cases hz : z ∈ boxFinsetBK d n
        · simp [forceSitesOccupied, hz]
        · simp [forceSitesOccupied, hz]
      exact Bool.eq_true_of_true_le (hopen ▸ hmono s(x, y))
  · rintro ⟨hadj, hnew⟩
    refine ⟨hadj, ?_⟩
    by_cases hold : siteToBond eta s(x, y) = true
    · unfold forceOpenFinset
      split <;> simp [hold]
    · have hxyNew :
          forceSitesOccupied (boxFinsetBK d n) eta x = true ∧
            forceSitesOccupied (boxFinsetBK d n) eta y = true := by
        simpa [siteToBond_mk, Bool.and_eq_true] using hnew
      have hxyOld : eta x = false ∨ eta y = false := by
        cases hxOld : eta x with
        | false => exact Or.inl rfl
        | true =>
            cases hyOld : eta y with
            | false => exact Or.inr rfl
            | true =>
                exfalso
                apply hold
                simp [siteToBond_mk, hxOld, hyOld]
      have hbox : x ∈ box d (n + 1) ∧ y ∈ box d (n + 1) := by
        rcases hxyOld with hxOld | hyOld
        · have hxBox : x ∈ box d n :=
            mem_box_of_forceSitesOccupied_true_of_false n eta x hxyNew.1 hxOld
          exact ⟨box_subset_box_succ n hxBox, adj_box_step hxBox hadj⟩
        · have hyBox : y ∈ box d n :=
            mem_box_of_forceSitesOccupied_true_of_false n eta y hxyNew.2 hyOld
          exact ⟨adj_box_step hyBox hadj.symm, box_subset_box_succ n hyBox⟩
      have hedge : s(x, y) ∈ siteForceEdges n eta := by
        rw [siteForceEdges, Finset.mem_filter]
        exact ⟨mk_mem_boxEdges hbox.1 hbox.2 hadj, hnew⟩
      exact forceOpenFinset_of_mem hedge (siteToBond eta)


theorem connected_siteForce_iff_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) (x y : Site d) :
    Connected d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x y ↔
      Connected d
        (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) x y := by
  unfold Connected
  rw [openSubgraph_siteForce_eq_forceOpen]


theorem cluster_siteForce_eq_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) (x : Site d) :
    cluster d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x =
      cluster d (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) x := by
  ext y
  exact connected_siteForce_iff_forceOpen n eta x y



theorem numInfiniteClusters_siteForce_eq_forceOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    numInfiniteClusters d
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) =
      numInfiniteClusters d
        (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) := by
  unfold numInfiniteClusters
  apply congrArg Set.encard
  ext C
  simp only [infiniteClusters, Set.mem_setOf_eq]
  constructor <;> rintro ⟨hC, x, rfl⟩
  · exact ⟨hC, x, cluster_siteForce_eq_forceOpen n eta x⟩
  · exact ⟨hC, x, (cluster_siteForce_eq_forceOpen n eta x).symm⟩



theorem siteForce_box_connected (n : ℕ) (eta : ConfigSpace (Site d))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    Connected d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x y := by
  have hle : forceOpenFinset (boxEdges d n) (siteToBond eta) ≤
      siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
        by_cases he : s(u, v) ∈ boxEdges d n
        · have huv := mem_boxEdges_iff.mp he
          simp [forceOpenFinset, he, siteToBond_mk, forceSitesOccupied,
            mem_boxFinsetBK_iff.mpr huv.1, mem_boxFinsetBK_iff.mpr huv.2.1]
        · rw [forceOpenFinset_of_notMem he]
          exact siteToBond_mono (fun z => by
            by_cases hz : z ∈ boxFinsetBK d n <;> simp [forceSitesOccupied, hz]) s(u, v)
  exact connected_mono hle (box_allOpen_connected (siteToBond eta) hx hy)



theorem numInfiniteClusters_siteForce_lt_of_twoMeetBox (n : ℕ)
    (eta : ConfigSpace (Site d))
    (hfin : numInfiniteClusters d (siteToBond eta) ≠ ⊤)
    {x y : Site d} (hxbox : x ∈ box d n) (hybox : y ∈ box d n)
    (hx : (cluster d (siteToBond eta) x).Infinite)
    (hy : (cluster d (siteToBond eta) y).Infinite)
    (hne : cluster d (siteToBond eta) x ≠ cluster d (siteToBond eta) y) :
    numInfiniteClusters d
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) <
      numInfiniteClusters d (siteToBond eta) := by
  rw [numInfiniteClusters_siteForce_eq_forceOpen]
  exact numInfiniteClusters_lt_of_merge (siteForceEdges n eta) (siteToBond eta)
    hfin x y hx hy hne
    ((connected_siteForce_iff_forceOpen n eta x y).1
      (siteForce_box_connected n eta hxbox hybox))



def SiteTwoMeetBox (n : ℕ) (k : ℕ∞) : Set (ConfigSpace (Site d)) :=
  siteToBond ⁻¹' twoMeetBox d n k



theorem exists_siteTwoMeetBox_pos
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    {k : ℕ∞} (hk2 : 2 ≤ k)
    (hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1) :
    ∃ n : ℕ, 0 < nu (SiteTwoMeetBox (d := d) n k) := by
  have hcover : {eta : ConfigSpace (Site d) |
      numInfiniteClusters d (siteToBond eta) = k} ⊆
      ⋃ n, SiteTwoMeetBox (d := d) n k := by
    intro eta heta
    have h := iEqLevel_subset_iUnion_twoMeetBox hk2 heta
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : nu (⋃ n, SiteTwoMeetBox (d := d) n k) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      nu (⋃ n, SiteTwoMeetBox (d := d) n k) ≤
          ∑' n, nu (SiteTwoMeetBox (d := d) n k) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle : nu {eta : ConfigSpace (Site d) |
      numInfiniteClusters d (siteToBond eta) = k} ≤
      nu (⋃ n, SiteTwoMeetBox (d := d) n k) := measure_mono hcover
  rw [hk, hunion0] at hle
  exact absurd hle (by norm_num)



theorem finite_constant_cluster_count_impossible
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    {k : ℕ∞} (hk2 : 2 ≤ k) (hktop : k ≠ ⊤)
    (hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1) : False := by
  obtain ⟨n, hnpos⟩ := exists_siteTwoMeetBox_pos nu hk2 hk
  let B : Set (ConfigSpace (Site d)) :=
    {eta | numInfiniteClusters d (siteToBond eta) < k}
  have hBmeas : MeasurableSet B := by
    exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
      (MeasurableSet.of_discrete)
  have hsub : SiteTwoMeetBox (d := d) n k ⊆
      (forceSitesOccupied (boxFinsetBK d n)) ⁻¹' B := by
    rintro eta ⟨hcount, x, y, hxbox, hybox, hx, hy, hne⟩
    change numInfiniteClusters d
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) < k
    have hfin : numInfiniteClusters d (siteToBond eta) ≠ ⊤ := by
      rw [hcount]
      exact hktop
    have hlt := numInfiniteClusters_siteForce_lt_of_twoMeetBox n eta hfin
      hxbox hybox hx hy hne
    rwa [hcount] at hlt
  have hBpos : 0 < nu B := positive_of_forceSitesOccupied_preimage
    nu epsilon hepsilon hinsert (boxFinsetBK d n) hBmeas hsub hnpos
  have hBzero : nu B = 0 := by
    apply le_antisymm
    · have hlevelSub : {eta | numInfiniteClusters d (siteToBond eta) = k} ⊆ Bᶜ := by
        intro eta heta
        simp only [Set.mem_compl_iff]
        change ¬ numInfiniteClusters d (siteToBond eta) < k
        rw [heta]
        exact lt_irrefl k
      have hfull : nu Bᶜ = 1 := le_antisymm prob_le_one (hk ▸ measure_mono hlevelSub)
      exact (prob_compl_eq_one_iff hBmeas).mp hfull |>.le
    · exact bot_le
  rw [hBzero] at hBpos
  exact (lt_irrefl 0) hBpos





theorem site_cluster_count_ae_lt_two_or_infinite
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site d)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    ∃ k : ℕ∞,
      nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1 ∧
        (¬ 2 ≤ k ∨ k = ⊤) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) := Measure.map siteToBond nu
  haveI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map measurable_siteToBond.aemeasurable
  have hmuergo : IsErgodic (G := Multiplicative (Site d)) mu :=
    siteToBond_isErgodic nu herg
  obtain ⟨k, hkmu⟩ := numInfiniteClusters_ae_const mu hmuergo
  have hbondLevelMeas : MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d omega = k} := by
    change MeasurableSet ((numInfiniteClusters d) ⁻¹' ({k} : Set ℕ∞))
    exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
  have hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1 := by
    change (Measure.map siteToBond nu)
      {omega | numInfiniteClusters d omega = k} = 1 at hkmu
    rw [Measure.map_apply measurable_siteToBond hbondLevelMeas] at hkmu
    exact hkmu
  refine ⟨k, hk, ?_⟩
  by_cases hk2 : 2 ≤ k
  · right
    by_contra hktop
    exact finite_constant_cluster_count_impossible nu epsilon hepsilon hinsert
      hk2 hktop hk
  · exact Or.inl hk2



theorem site_cluster_count_ae_one_or_infinite
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site d)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (hperco : nu {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1) :
    nu {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 ∨
      nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤} = 1 := by
  obtain ⟨k, hk, hkCases⟩ := site_cluster_count_ae_lt_two_or_infinite
    nu herg epsilon hepsilon hinsert
  rcases hkCases with hk2 | hktop
  · have hkle : k ≤ 1 := enat_le_one_of_not_two hk2
    have hkne : k ≠ 0 := by
      intro hkzero
      have hposMeas : MeasurableSet
          {eta : ConfigSpace (Site d) |
            1 ≤ numInfiniteClusters d (siteToBond eta)} := by
        change MeasurableSet
          ((numInfiniteClusters d ∘ siteToBond) ⁻¹' Set.Ici 1)
        exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
          (MeasurableSet.of_discrete)
      have hcomplZero : nu {eta : ConfigSpace (Site d) |
          1 ≤ numInfiniteClusters d (siteToBond eta)}ᶜ = 0 := by
        rw [measure_compl hposMeas (measure_ne_top nu _), hperco]
        simp
      have hsub : {eta : ConfigSpace (Site d) |
          numInfiniteClusters d (siteToBond eta) = k} ⊆
          {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)}ᶜ := by
        intro eta heta
        simp only [Set.mem_setOf_eq] at heta
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro hpos
        rw [heta, hkzero] at hpos
        norm_num at hpos
      have hle : nu {eta : ConfigSpace (Site d) |
          numInfiniteClusters d (siteToBond eta) = k} ≤
          nu {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)}ᶜ :=
        measure_mono hsub
      rw [hk, hcomplZero] at hle
      exact one_ne_zero (le_antisymm hle bot_le)
    have hkone : k = 1 := le_antisymm hkle (ENat.one_le_iff_ne_zero.mpr hkne)
    left
    rwa [hkone] at hk
  · right
    rwa [hktop] at hk

end StatMech.FrontierA
