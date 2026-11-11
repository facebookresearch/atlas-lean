/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredDomChain
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneErgodic
/-!
# Two-point connectivity with and without percolation

For a measure on bond configurations of `ℤ^d` with at most one infinite cluster, positive
percolation gives a uniform positive lower bound on the two-point connectivity; without
percolation the two-point connectivity to far points tends to zero uniformly.

## i. Overview

If there is almost surely at most one infinite cluster, two sites that both lie in infinite
clusters are connected. With the FKG inequality for the events `{x ↔ ∞}` and translation
invariance, `P(0 ↔ x) ≥ P(0 ↔ ∞, x ↔ ∞) ≥ θ²` for every `x`. Conversely, `0 ↔ x` with `x`
outside the box of radius `n` forces a connection from the origin to the boundary of that box,
whose probability tends to `θ`; so if `θ = 0` the connectivity to far points is uniformly small.
The FKG inequality, translation invariance and uniqueness of the infinite cluster are hypotheses
of `infiniteTwoPoint_uniform_pos_of_fkg_unique`.

## ii. Key results

- `infiniteTwoPoint_uniform_pos_of_fkg_unique` : `P(0 ↔ x) ≥ θ²` for all `x`, given FKG,
  translation invariance and at most one infinite cluster.
- `boxBdryConnEvent_real_tendsto_percolation` : the probability that the origin is connected
  to the boundary of the box of radius `n` tends to `θ`.
- `infiniteTwoPoint_uniform_decay_of_no_percolation` : if `θ = 0`, then `P(0 ↔ x) → 0`
  uniformly as `x → ∞`.

## iii. Table of contents

- A. Two-point connectivity and infinite clusters
- B. Box-boundary connections and the percolation probability

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 5.1.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## A. Two-point connectivity and infinite clusters -/

/-- The two-point connectivity `μ(x ↔ y)` of a measure on bond configurations of `ℤ^d`. -/
noncomputable def infiniteTwoPointReal
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) (x y : Site d) : ℝ :=
  μ.real {ω | StatMech.Lattice.Connected d ω x y}

/-- The event `{x ↔ ∞}` that the open cluster of `x` is infinite. -/
def clusterInfiniteEvent (d : ℕ) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (cluster d ω x).Infinite}

/-- If `x` and `y` both lie in infinite clusters, either they are connected or there are at least
two infinite clusters. -/
lemma two_infinite_clusters_of_not_connected (x y : Site d) :
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

/-- With at most one infinite cluster almost surely, `μ(x ↔ ∞, y ↔ ∞) ≤ μ(x ↔ y)`. -/
lemma infinite_cluster_inter_le_twoPoint
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

/-- If `μ` satisfies the FKG inequality for the events `{x ↔ ∞}` (`hPA`), is translation
invariant on them (`hTI`), has at most one infinite cluster almost surely (`huniq`), and
percolates (`htheta`), then `μ(0 ↔ x) ≥ θ²` for every `x`. -/
lemma infiniteTwoPoint_uniform_pos_of_fkg_unique
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

/-! ## B. Box-boundary connections and the percolation probability -/

/-- For any finite measure, the probability that the origin is connected to the complement of the
box of radius `n - 1` tends to the percolation probability. -/
lemma crossingEvent_real_tendsto_percolation
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ] :
    Tendsto (fun n => μ.real (crossingEvent d n)) atTop
      (nhds (μ.real (percolationEvent d))) := by
  have hmeas : ∀ n, NullMeasurableSet (crossingEvent d n) μ :=
    fun n => (Percolation.measurableSet_crossingEvent n).nullMeasurableSet
  have hanti : Antitone (fun n => crossingEvent d n) :=
    fun m n hmn => crossingEvent_antitone m n hmn
  have hfin : ∃ i, μ (crossingEvent d i) ≠ ⊤ := ⟨0, measure_ne_top μ _⟩
  have htend := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti hfin
  rw [iInter_crossingEvent_eq_percolationEvent] at htend
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp htend

/-- For any finite measure, the probability that the origin is connected to the boundary of the box
of radius `n` inside the box tends to the percolation probability. -/
lemma boxBdryConnEvent_real_tendsto_percolation
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

/-- A connection from the origin to a site outside the box passes through the box boundary. -/
lemma connectionEvent_subset_boxBdryConnEvent (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hx : x ∉ box d n) :
    {ω | StatMech.Lattice.Connected d ω (origin d) x} ⊆ boxBdryConnEvent d n := by
  intro ω hconn
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_ofPred_eq]
  exact boxBdryConn_of_crossing n hn ω hx hconn

/-- Without percolation, the two-point connectivity from the origin tends to zero uniformly: for
every `ε > 0` there is `n` with `μ(0 ↔ x) < ε` for all `x` outside the box of radius `n`. -/
lemma infiniteTwoPoint_uniform_decay_of_no_percolation
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
