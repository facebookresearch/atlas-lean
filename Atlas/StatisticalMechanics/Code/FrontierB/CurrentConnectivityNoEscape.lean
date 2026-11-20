/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.FrontierB.CurrentConnectivityDiagonal
import Code.Percolation.BurtonKeaneErgodic

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}



noncomputable def traceBoundaryConnectionEvent (m : ℕ) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  ⋃ z ∈ (vertexBoundary_finite d m).toFinset, boxConnectionEvent m x z

theorem mem_traceBoundaryConnectionEvent
    {m : ℕ} {x : Site d} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ traceBoundaryConnectionEvent m x ↔ connBdry d m ω x := by
  simp only [traceBoundaryConnectionEvent, Set.mem_iUnion,
    Set.Finite.mem_toFinset, boxConnectionEvent, mem_withinConnEvent]
  constructor
  · rintro ⟨z, hzbdry, hx, hz, hconn⟩
    exact ⟨hx, z, hz, hzbdry, hconn⟩
  · rintro ⟨hx, z, hz, hzbdry, hconn⟩
    exact ⟨z, hzbdry, hx, hz, hconn⟩

theorem isClopen_traceBoundaryConnectionEvent (m : ℕ) (x : Site d) :
    IsClopen (traceBoundaryConnectionEvent m x) := by
  unfold traceBoundaryConnectionEvent
  exact isClopen_biUnion_finset fun z _ => isClopen_boxConnectionEvent m x z




noncomputable def twoArmDisconnectedTraceEvent (m : ℕ) (x y : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  (traceBoundaryConnectionEvent m x ∩ traceBoundaryConnectionEvent m y) \
    boxConnectionEvent m x y

theorem mem_twoArmDisconnectedTraceEvent
    {m : ℕ} {x y : Site d} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ twoArmDisconnectedTraceEvent m x y ↔
      connBdry d m ω x ∧ connBdry d m ω y ∧
        ω ∉ boxConnectionEvent m x y := by
  simp only [twoArmDisconnectedTraceEvent, Set.mem_diff, Set.mem_inter_iff,
    mem_traceBoundaryConnectionEvent, and_assoc]

theorem isClopen_twoArmDisconnectedTraceEvent (m : ℕ) (x y : Site d) :
    IsClopen (twoArmDisconnectedTraceEvent m x y) :=
  ((isClopen_traceBoundaryConnectionEvent m x).inter
    (isClopen_traceBoundaryConnectionEvent m y)).diff
      (isClopen_boxConnectionEvent m x y)



theorem mem_traceBoundaryConnectionEvent_of_connected_outside
    {m : ℕ} (hm : 1 ≤ m) {ω : ConfigSpace (Sym2 (Site d))} {x z : Site d}
    (hx : x ∈ box d (m - 1)) (hz : z ∉ box d (m - 1))
    (hconn : Connected d ω x z) :
    ω ∈ traceBoundaryConnectionEvent m x := by
  classical
  rw [mem_traceBoundaryConnectionEvent]
  obtain ⟨p⟩ := hconn
  obtain ⟨a, b, ha, hb, hab, ⟨w⟩⟩ :=
    firstExit p (box d (m - 1)) hx hz
  have hxm : x ∈ box d m := box_mono d (by omega) hx
  have ham : a ∈ box d m := box_mono d (by omega) ha
  have hbm : b ∈ box d m := by
    have hstep := adj_box_step (m := m - 1) ha hab.1
    rwa [show m - 1 + 1 = m by omega] at hstep
  have hbBoundary : b ∈ vertexBoundary d m := ⟨hbm, hb⟩
  have hxa : ConnectedWithin d ω (box d m) ⟨x, hxm⟩ ⟨a, ham⟩ :=
    connectedWithin_mono_set' ω (box_mono d (by omega))
      (x := ⟨x, hx⟩) (y := ⟨a, ha⟩) ⟨w⟩
  have habm : (openSubgraphInduce d ω (box d m)).Adj ⟨a, ham⟩ ⟨b, hbm⟩ := by
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    exact hab
  exact ⟨hxm, b, hbm, hbBoundary,
    hxa.trans (SimpleGraph.Adj.reachable habm)⟩



theorem currentPairTraceBoxGate_diff_subset_twoArm
    {Q : Set (ConfigSpace (Sym2 (Site d)))} {m k : ℕ} {x y : Site d}
    (hm : 1 ≤ m) (hx : x ∈ box d (m - 1)) (hy : y ∈ box d (m - 1))
    (_hmk : m ≤ k) :
    currentPairTraceBoxGate Q k x y \ currentPairTraceBoxGate Q m x y ⊆
      superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent m x y := by
  intro pair hpair
  let ω := superposedCurrentTrace pair
  have hQ : ω ∈ Q := hpair.1.1
  have hk : ω ∈ boxConnectionEvent k x y := hpair.1.2
  have hnotm : ω ∉ boxConnectionEvent m x y := by
    intro hmconn
    exact hpair.2 ⟨hQ, hmconn⟩
  obtain ⟨_, _, hkconn⟩ := hk
  obtain ⟨p⟩ := hkconn.connected
  have hout : ∃ z ∈ p.support, z ∉ box d m := by
    by_contra h
    simp only [not_exists, not_and] at h
    have hsupp : ∀ z ∈ p.support, z ∈ box d m := by
      intro z hz
      by_contra hzout
      exact h z hz hzout
    apply hnotm
    exact ⟨box_mono d (by omega) hx, box_mono d (by omega) hy,
      ⟨p.induce (box d m) hsupp⟩⟩
  obtain ⟨z, hzp, hzout⟩ := hout
  have hzout' : z ∉ box d (m - 1) := fun hz =>
    hzout (box_mono d (by omega) hz)
  have hxz : Connected d ω x z := (p.takeUntil z hzp).reachable
  have hyz : Connected d ω y z := (p.dropUntil z hzp).reverse.reachable
  rw [Set.mem_preimage, mem_twoArmDisconnectedTraceEvent]
  exact ⟨mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hx hzout' hxz),
    mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hy hzout' hyz),
    hnotm⟩



theorem twoArmDisconnectedTraceEvent_antitone_of_mem
    {m n : ℕ} {x y : Site d} (hm : 1 ≤ m)
    (hx : x ∈ box d (m - 1)) (hy : y ∈ box d (m - 1)) (hmn : m ≤ n) :
    twoArmDisconnectedTraceEvent n x y ⊆
      twoArmDisconnectedTraceEvent m x y := by
  intro ω hω
  rw [mem_twoArmDisconnectedTraceEvent] at hω ⊢
  obtain ⟨⟨_, zx, _, hzxBoundary, hxzx⟩,
    ⟨_, zy, _, hzyBoundary, hyzy⟩, hnconn⟩ := hω
  have hmnPred : m - 1 ≤ n - 1 := Nat.sub_le_sub_right hmn 1
  have hzxout : zx ∉ box d (m - 1) := fun hzx =>
    hzxBoundary.2 (box_mono d hmnPred hzx)
  have hzyout : zy ∉ box d (m - 1) := fun hzy =>
    hzyBoundary.2 (box_mono d hmnPred hzy)
  refine ⟨mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hx hzxout hxzx.connected),
    mem_traceBoundaryConnectionEvent.1
      (mem_traceBoundaryConnectionEvent_of_connected_outside hm hy hzyout hyzy.connected), ?_⟩
  intro hmconn
  exact hnconn (boxConnectionEvent_mono x y hmn hmconn)


def distinctInfiniteClusterEvent (x y : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  { ω | (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧
    ¬ Connected d ω x y }



theorem twoArmDisconnectedTraceEvent_tail_antitone
    {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R) :
    Antitone (fun n => twoArmDisconnectedTraceEvent (R + n + 1) x y) := by
  intro m n hmn
  apply twoArmDisconnectedTraceEvent_antitone_of_mem (by omega)
  · simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R m) hx
  · simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R m) hy
  · omega



theorem iInter_twoArmDisconnectedTraceEvent
    {R : ℕ} {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R) :
    (⋂ n, twoArmDisconnectedTraceEvent (R + n + 1) x y) =
      distinctInfiniteClusterEvent x y := by
  ext ω
  simp only [Set.mem_iInter, distinctInfiniteClusterEvent, Set.mem_setOf_eq]
  constructor
  · intro h
    have hnotconn : ¬ Connected d ω x y := by
      intro hconn
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp
        ((mem_iUnion_boxConnectionEvent_iff_connected ω x y).2 hconn)
      have hlarge := boxConnectionEvent_mono x y (by omega : m ≤ R + m + 1) hm
      exact (mem_twoArmDisconnectedTraceEvent.1 (h m)).2.2 hlarge
    have hxinf : (cluster d ω x).Infinite := by
      rw [cluster_infinite_iff]
      intro m
      obtain ⟨_, z, _, hzBoundary, hxz⟩ :=
        (mem_twoArmDisconnectedTraceEvent.1 (h m)).1
      refine ⟨z, ?_, hxz.connected⟩
      intro hzm
      exact hzBoundary.2 (box_mono d (by omega) hzm)
    have hyinf : (cluster d ω y).Infinite := by
      rw [cluster_infinite_iff]
      intro m
      obtain ⟨_, z, _, hzBoundary, hyz⟩ :=
        (mem_twoArmDisconnectedTraceEvent.1 (h m)).2.1
      refine ⟨z, ?_, hyz.connected⟩
      intro hzm
      exact hzBoundary.2 (box_mono d (by omega) hzm)
    exact ⟨hxinf, hyinf, hnotconn⟩
  · rintro ⟨hxinf, hyinf, hnotconn⟩ n
    have hxr : x ∈ box d (R + n + 1 - 1) := by
      simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R n) hx
    have hyr : y ∈ box d (R + n + 1 - 1) := by
      simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R n) hy
    obtain ⟨zx, hzxout, hxzx⟩ :=
      (cluster_infinite_iff ω x).1 hxinf (R + n + 1 - 1)
    obtain ⟨zy, hzyout, hyzy⟩ :=
      (cluster_infinite_iff ω y).1 hyinf (R + n + 1 - 1)
    rw [mem_twoArmDisconnectedTraceEvent]
    refine ⟨mem_traceBoundaryConnectionEvent.1
        (mem_traceBoundaryConnectionEvent_of_connected_outside (by omega) hxr hzxout hxzx),
      mem_traceBoundaryConnectionEvent.1
        (mem_traceBoundaryConnectionEvent_of_connected_outside (by omega) hyr hzyout hyzy), ?_⟩
    intro hbox
    exact hnotconn hbox.2.2.connected


theorem distinctInfiniteClusterEvent_subset_atLeastTwoInfinite (x y : Site d) :
    distinctInfiniteClusterEvent x y ⊆ atLeastTwoInfinite d := by
  intro ω hω
  obtain ⟨hxinf, hyinf, hxy⟩ := hω
  have hne : cluster d ω x ≠ cluster d ω y := by
    intro heq
    apply hxy
    rw [← mem_cluster, heq]
    exact self_mem_cluster ω y
  have hpair : ({cluster d ω x, cluster d ω y} : Set (Set (Site d))) ⊆
      infiniteClusters d ω := by
    intro C hC
    rcases hC with (rfl | hC)
    · exact ⟨hxinf, x, rfl⟩
    · have : C = cluster d ω y := by simpa using hC
      subst C
      exact ⟨hyinf, y, rfl⟩
  change 2 ≤ numInfiniteClusters d ω
  unfold numInfiniteClusters
  rw [← Set.encard_pair hne]
  exact Set.encard_le_encard hpair

private theorem cnx_probabilityMeasure_coe_apply_eq_real
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (A : Set Ω) :
    ((μ A : NNReal) : ℝ) = (μ : Measure Ω).real A := by
  rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact (ENNReal.coe_toReal _).symm

private theorem cnx_independentSuperposedTraceLaw_real
    (μ ν : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    {A : Set (ConfigSpace (Sym2 (Site d)))} (hA : MeasurableSet A) :
    (independentSuperposedTraceLaw μ ν : Measure _).real A =
      (μ.prod ν : Measure _).real (superposedCurrentTrace ⁻¹' A) := by
  rw [← cnx_probabilityMeasure_coe_apply_eq_real
      (independentSuperposedTraceLaw μ ν) A,
    ← cnx_probabilityMeasure_coe_apply_eq_real (μ.prod ν)
      (superposedCurrentTrace ⁻¹' A)]
  exact congrArg (fun z : NNReal => (z : ℝ))
    (ProbabilityMeasure.map_apply (μ.prod ν)
      continuous_superposedCurrentTrace.measurable.aemeasurable hA)



theorem WeakCurrentConverges.pairTraceClopen_real
    {μ ν : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {μLim νLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hμ : WeakCurrentConverges μ μLim)
    (hν : WeakCurrentConverges ν νLim)
    {A : Set (ConfigSpace (Sym2 (Site d)))} (hA : IsClopen A) :
    Tendsto
      (fun k => ((μ k).prod (ν k) : Measure _).real
        (superposedCurrentTrace ⁻¹' A)) atTop
      (nhds ((μLim.prod νLim : Measure _).real
        (superposedCurrentTrace ⁻¹' A))) := by
  have htrace := independentSuperposedTraceLaw_tendsto hμ hν
  have hport : Tendsto
      (fun k => (independentSuperposedTraceLaw (μ k) (ν k) : Measure _).real A)
        atTop
      (nhds ((independentSuperposedTraceLaw μLim νLim : Measure _).real A)) :=
    (show WeakConvergesTo
      (fun k => independentSuperposedTraceLaw (μ k) (ν k))
      (independentSuperposedTraceLaw μLim νLim) from htrace).tendsto_real_of_isClopen hA
  have hAmeas : MeasurableSet A := hA.isOpen.measurableSet
  simpa only [cnx_independentSuperposedTraceLaw_real (d := d) (hA := hAmeas)] using hport




theorem currentPairConnectivityNoEscape_of_uniqueInfiniteCluster
    {μ ν : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {μLim νLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hμ : WeakCurrentConverges μ μLim)
    (hν : WeakCurrentConverges ν νLim)
    (hunique : (independentSuperposedTraceLaw μLim νLim : Measure _)
      (atLeastTwoInfinite d) = 0)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    CurrentPairConnectivityNoEscape μ ν Q x y := by
  obtain ⟨R, hR⟩ := Percolation.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxR : x ∈ box d R := hR (by simp)
  have hyR : y ∈ box d R := hR (by simp)
  let traceLim := independentSuperposedTraceLaw μLim νLim
  have htail : Antitone (fun n => twoArmDisconnectedTraceEvent (R + n + 1) x y) :=
    twoArmDisconnectedTraceEvent_tail_antitone hxR hyR
  have hmeas : ∀ n, NullMeasurableSet
      (twoArmDisconnectedTraceEvent (R + n + 1) x y) (traceLim : Measure _) :=
    fun n =>
      (isClopen_twoArmDisconnectedTraceEvent
        (R + n + 1) x y).isOpen.measurableSet.nullMeasurableSet
  have hdistinctZero : (traceLim : Measure _) (distinctInfiniteClusterEvent x y) = 0 := by
    apply le_antisymm
    · calc
        (traceLim : Measure _) (distinctInfiniteClusterEvent x y) ≤
            (traceLim : Measure _) (atLeastTwoInfinite d) :=
          measure_mono (distinctInfiniteClusterEvent_subset_atLeastTwoInfinite x y)
        _ = 0 := hunique
    · exact bot_le
  have htailMeasure : Tendsto
      (fun n => (traceLim : Measure _) (twoArmDisconnectedTraceEvent (R + n + 1) x y))
      atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop (μ := (traceLim : Measure _)) hmeas htail
      ⟨0, measure_ne_top (traceLim : Measure _)
        (twoArmDisconnectedTraceEvent (R + 0 + 1) x y)⟩
    rw [iInter_twoArmDisconnectedTraceEvent hxR hyR, hdistinctZero] at h
    exact h
  have htailReal : Tendsto
      (fun n => (traceLim : Measure _).real
        (twoArmDisconnectedTraceEvent (R + n + 1) x y)) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp htailMeasure
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htailReal) δ hδ
  let M := R + N + 1
  have hlimitSmall : (traceLim : Measure _).real
      (twoArmDisconnectedTraceEvent M x y) < δ := by
    have hclose := hN N (le_refl N)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hclose
    simpa only [M] using hclose
  refine ⟨M, ?_⟩
  intro m hmM
  have hMpos : 1 ≤ M := by dsimp [M]; omega
  have hxM : x ∈ box d (M - 1) := by
    dsimp [M]
    simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R N) hxR
  have hyM : y ∈ box d (M - 1) := by
    dsimp [M]
    simpa only [Nat.add_sub_cancel] using box_mono d (Nat.le_add_right R N) hyR
  have htwoMono : twoArmDisconnectedTraceEvent m x y ⊆
      twoArmDisconnectedTraceEvent M x y :=
    twoArmDisconnectedTraceEvent_antitone_of_mem hMpos hxM hyM hmM
  have hport := hμ.pairTraceClopen_real hν
    (isClopen_twoArmDisconnectedTraceEvent M x y)
  have hMMeas : MeasurableSet (twoArmDisconnectedTraceEvent M x y) :=
    (isClopen_twoArmDisconnectedTraceEvent M x y).isOpen.measurableSet
  have hlimitPair : (μLim.prod νLim : Measure _).real
      (superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent M x y) < ε := by
    rw [← cnx_independentSuperposedTraceLaw_real μLim νLim hMMeas]
    change (traceLim : Measure _).real (twoArmDisconnectedTraceEvent M x y) < ε
    exact hlimitSmall.trans (by dsimp [δ]; linarith)
  have heventuallySmall : ∀ᶠ k in atTop,
      (((μ k).prod (ν k) : Measure _).real
        (superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent M x y)) < ε :=
    (tendsto_order.1 hport).2 ε hlimitPair
  filter_upwards [heventuallySmall, eventually_ge_atTop m] with k hkSmall hmk
  have hescape := currentPairTraceBoxGate_diff_subset_twoArm
    (Q := Q) (m := m) (k := k) (x := x) (y := y)
    (hMpos.trans hmM) (box_mono d (by omega) hxM)
      (box_mono d (by omega) hyM) hmk
  have hsubset : currentPairTraceBoxGate Q k x y \
        currentPairTraceBoxGate Q m x y ⊆
      superposedCurrentTrace ⁻¹' twoArmDisconnectedTraceEvent M x y :=
    hescape.trans (Set.preimage_mono htwoMono)
  exact (measureReal_mono hsubset (by finiteness)).trans_lt hkSmall

end StatMech.FrontierB
