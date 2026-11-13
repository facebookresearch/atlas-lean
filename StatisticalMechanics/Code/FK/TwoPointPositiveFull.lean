/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FK.WiredDomChain
import Code.Percolation.BurtonKeaneErgodic

open MeasureTheory Filter Topology

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}



noncomputable def infiniteTwoPointReal
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) (x y : Site d) : ℝ :=
  μ.real {ω | StatMech.Lattice.Connected d ω x y}


def clusterInfiniteEvent (d : ℕ) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (cluster d ω x).Infinite}

theorem measurableSet_clusterInfiniteEvent (x : Site d) :
    MeasurableSet (clusterInfiniteEvent d x) :=
  measurableSet_clusterInfinite x



theorem two_infinite_clusters_of_not_connected (x y : Site d) :
    clusterInfiniteEvent d x ∩ clusterInfiniteEvent d y ⊆
      {ω | StatMech.Lattice.Connected d ω x y} ∪ atLeastTwoInfinite d := by
  intro ω hω
  rcases hω with ⟨hx, hy⟩
  by_cases hxy : StatMech.Lattice.Connected d ω x y
  · exact Or.inl hxy
  · right
    have hne : cluster d ω x ≠ cluster d ω y := by
      intro heq
      apply hxy
      rw [← mem_cluster]
      rw [heq]
      exact self_mem_cluster ω y
    have hpair : ({cluster d ω x, cluster d ω y} : Set (Set (Site d))) ⊆
        infiniteClusters d ω := by
      intro C hC
      rcases hC with (rfl | hC)
      · exact ⟨hx, x, rfl⟩
      · have : C = cluster d ω y := by simpa using hC
        subst C
        exact ⟨hy, y, rfl⟩
    change 2 ≤ numInfiniteClusters d ω
    unfold numInfiniteClusters
    rw [← Set.encard_pair hne]
    exact Set.encard_le_encard hpair



theorem infinite_cluster_inter_le_twoPoint
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ]
    (huniq : μ (atLeastTwoInfinite d) = 0) (x y : Site d) :
    μ.real (clusterInfiniteEvent d x ∩ clusterInfiniteEvent d y) ≤
      infiniteTwoPointReal μ x y := by
  have hsub := two_infinite_clusters_of_not_connected (d := d) x y
  have hle : μ (clusterInfiniteEvent d x ∩ clusterInfiniteEvent d y) ≤
      μ {ω | StatMech.Lattice.Connected d ω x y} := by
    calc
      μ (clusterInfiniteEvent d x ∩ clusterInfiniteEvent d y)
          ≤ μ ({ω | StatMech.Lattice.Connected d ω x y} ∪ atLeastTwoInfinite d) :=
        measure_mono hsub
      _ ≤ μ {ω | StatMech.Lattice.Connected d ω x y} + μ (atLeastTwoInfinite d) :=
        measure_union_le _ _
      _ = μ {ω | StatMech.Lattice.Connected d ω x y} := by rw [huniq, add_zero]
  exact ENNReal.toReal_mono (measure_ne_top μ _) hle










theorem infiniteTwoPoint_uniform_pos_of_fkg_unique
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ]
    (hPA : ∀ x : Site d,
      μ.real (clusterInfiniteEvent d (origin d)) *
          μ.real (clusterInfiniteEvent d x) ≤
        μ.real (clusterInfiniteEvent d (origin d) ∩ clusterInfiniteEvent d x))
    (hTI : ∀ x : Site d,
      μ.real (clusterInfiniteEvent d x) =
        μ.real (clusterInfiniteEvent d (origin d)))
    (huniq : μ (atLeastTwoInfinite d) = 0)
    (htheta : 0 < μ.real (percolationEvent d)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Site d,
      c ≤ infiniteTwoPointReal μ (origin d) x := by
  have hperco : percolationEvent d = clusterInfiniteEvent d (origin d) := rfl
  let c := μ.real (percolationEvent d) ^ 2
  refine ⟨c, sq_pos_of_pos htheta, ?_⟩
  intro x
  have hfk := hPA x
  rw [hTI x, ← hperco] at hfk
  dsimp [c]
  rw [pow_two]
  exact hfk.trans (by
    rw [hperco]
    exact infinite_cluster_inter_le_twoPoint μ huniq (origin d) x)





theorem crossingEvent_real_tendsto_percolation
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ] :
    Tendsto (fun n => μ.real (crossingEvent d n)) atTop
      (nhds (μ.real (percolationEvent d))) := by
  have hmeas : ∀ n, NullMeasurableSet (crossingEvent d n) μ :=
    fun n => (measurableSet_crossingEvent n).nullMeasurableSet
  have hanti : Antitone (fun n => crossingEvent d n) :=
    fun m n hmn => crossingEvent_antitone m n hmn
  have hfin : ∃ i, μ (crossingEvent d i) ≠ ⊤ := ⟨0, measure_ne_top μ _⟩
  have htend := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti hfin
  rw [iInter_crossingEvent_eq_percolationEvent] at htend
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend



theorem boxBdryConnEvent_real_tendsto_percolation
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ] :
    Tendsto (fun n => μ.real (boxBdryConnEvent d n)) atTop
      (nhds (μ.real (percolationEvent d))) := by
  have htail := crossingEvent_real_tendsto_percolation (d := d) μ
  have htailShift := htail.comp (tendsto_add_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htailShift htail ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact measureReal_mono (crossingEvent_succ_subset_boxBdryConnEvent n hn)
  · filter_upwards with n
    exact measureReal_mono (boxBdryConnEvent_subset_crossingEvent n)



theorem connectionEvent_subset_boxBdryConnEvent (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hx : x ∉ box d n) :
    {ω | StatMech.Lattice.Connected d ω (origin d) x} ⊆ boxBdryConnEvent d n := by
  intro ω hconn
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq]
  exact boxBdryConn_of_crossing n hn ω hx hconn







theorem infiniteTwoPoint_uniform_decay_of_no_percolation
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ]
    (htheta : μ.real (percolationEvent d) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 1 ≤ n ∧ ∀ x : Site d, x ∉ box d n →
      infiniteTwoPointReal μ (origin d) x < ε := by
  intro ε hε
  have htend : Tendsto (fun n => μ.real (boxBdryConnEvent d n)) atTop (nhds 0) := by
    simpa [htheta] using boxBdryConnEvent_real_tendsto_percolation (d := d) μ
  have hevent : ∀ᶠ n in atTop, μ.real (boxBdryConnEvent d n) < ε :=
    (tendsto_order.1 htend).2 ε hε
  obtain ⟨n, hnε, hn⟩ := (hevent.and (eventually_ge_atTop 1)).exists
  refine ⟨n, hn, ?_⟩
  intro x hx
  exact (measureReal_mono (connectionEvent_subset_boxBdryConnEvent n hn x hx)).trans_lt hnε

end FK

end StatMech
