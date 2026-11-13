/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierB.CurrentConnectivityNoEscape
import Code.FrontierB.FreeParityErrorReduction
import Code.Lattice.PlanarTopology

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem isOpen_connectedEvent (x y : Site d) :
    IsOpen {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y} := by
  rw [<- iUnion_boxConnectionEvent x y]
  exact isOpen_iUnion fun n => (isClopen_boxConnectionEvent n x y).isOpen



noncomputable def finiteClusterNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) : Finset (Site d) := by
  classical
  let K := hfin.toFinset
  exact K ∪ K.biUnion (fun z => (hypercubicLattice d).neighborFinset z)

theorem finiteCluster_mem_finiteClusterNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) :
    cluster d omega x ⊆
      (finiteClusterNeighborhood omega x hfin : Set (Site d)) := by
  intro z hz
  apply Finset.mem_coe.2
  apply Finset.mem_union_left
  exact (hfin.mem_toFinset).2 hz

theorem neighbor_mem_finiteClusterNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) {z w : Site d}
    (hz : z ∈ cluster d omega x) (hzw : (hypercubicLattice d).Adj z w) :
    w ∈ finiteClusterNeighborhood omega x hfin := by
  classical
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨z, (hfin.mem_toFinset).2 hz,
    (SimpleGraph.mem_neighborFinset (hypercubicLattice d) z w).2 hzw⟩

theorem clusterWithin_finiteClusterNeighborhood_eq_cluster
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) :
    clusterWithin d omega (finiteClusterNeighborhood omega x hfin : Set (Site d)) x =
      cluster d omega x := by
  classical
  let S : Set (Site d) := finiteClusterNeighborhood omega x hfin
  ext y
  constructor
  · rintro hy
    exact hy.2.2.connected
  · intro hy
    obtain ⟨w⟩ := (mem_cluster.1 hy)
    have hsupp : ∀ z ∈ w.support, z ∈ S := by
      intro z hz
      apply finiteCluster_mem_finiteClusterNeighborhood omega x hfin
      exact mem_cluster.2 (w.takeUntil z hz).reachable
    have hxS : x ∈ S := hsupp x w.start_mem_support
    have hyS : y ∈ S := hsupp y w.end_mem_support
    exact ⟨hyS, hxS, ⟨w.induce S hsupp⟩⟩

theorem isClopen_finiteClusterEvent
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) :
    IsClopen (clusterEvent d
      (finiteClusterNeighborhood omega x hfin : Set (Site d)) x
      (cluster d omega x)) := by
  classical
  let S := finiteClusterNeighborhood omega x hfin
  let K := hfin.toFinset
  have hxS : x ∈ (S : Set (Site d)) :=
    finiteCluster_mem_finiteClusterNeighborhood omega x hfin
      (self_mem_cluster omega x)
  have hK : (K : Set (Site d)) = cluster d omega x := hfin.coe_toFinset
  have hdep := clusterEvent_dependsOn (d := d) (S := S) (K := K) hxS
  rw [hK] at hdep
  rw [eq_cylinder_restrict_image _ _ hdep]
  exact isClopen_cylinderEvent _ _

theorem connected_clusterEvent_imp_mem
    (omega eta : ConfigSpace (Sym2 (Site d))) (x y : Site d)
    (hfin : (cluster d omega x).Finite)
    (heta : eta ∈ clusterEvent d
      (finiteClusterNeighborhood omega x hfin : Set (Site d)) x
      (cluster d omega x))
    (hxy : Connected d eta x y) : y ∈ cluster d omega x := by
  classical
  let S : Set (Site d) := finiteClusterNeighborhood omega x hfin
  have hcluster : clusterWithin d eta S x = cluster d omega x := heta
  obtain ⟨w⟩ := hxy
  have hx : x ∈ cluster d omega x := self_mem_cluster omega x
  have trap : ∀ {u v : Site d}, (openSubgraph d eta).Walk u v →
      u ∈ cluster d omega x → v ∈ cluster d omega x := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | @cons u v z huv p ih =>
      intro hu
      have hvS : v ∈ S := by
        apply neighbor_mem_finiteClusterNeighborhood omega x hfin hu
        exact (show IsOpenEdge d eta u v from huv).1
      have huWithin : u ∈ clusterWithin d eta S x := by
        rw [hcluster]
        exact hu
      have hvWithin : v ∈ clusterWithin d eta S x :=
        clusterWithin_closed huWithin hvS (show IsOpenEdge d eta u v from huv)
      have hv : v ∈ cluster d omega x := by rwa [hcluster] at hvWithin
      exact ih hv
  exact trap w hx



theorem frontier_connectedEvent_subset_distinctInfiniteClusterEvent (x y : Site d) :
    frontier {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y} ⊆
      distinctInfiniteClusterEvent x y := by
  intro omega homega
  have hopen := isOpen_connectedEvent x y
  have hnotconn : ¬ Connected d omega x y := by
    intro hconn
    apply homega.2
    rw [hopen.interior_eq]
    exact hconn
  have hinfinite (z w : Site d) (hzw : ¬ Connected d omega z w)
      (hclosure : omega ∈ closure
        {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta z w}) :
      (cluster d omega z).Infinite := by
    intro hfin
    let U := clusterEvent d
      (finiteClusterNeighborhood omega z hfin : Set (Site d)) z
      (cluster d omega z)
    have homegaU : omega ∈ U :=
      clusterWithin_finiteClusterNeighborhood_eq_cluster omega z hfin
    have hUopen : IsOpen U := (isClopen_finiteClusterEvent omega z hfin).isOpen
    have hdisj : Disjoint U
        {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta z w} := by
      rw [Set.disjoint_left]
      intro eta heta hconn
      exact hzw (mem_cluster.1
        (connected_clusterEvent_imp_mem omega eta z w hfin heta hconn))
    have hnotclosure : omega ∉ closure
        {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta z w} := by
      intro hclosure'
      obtain ⟨eta, hetaU, hetaConn⟩ :=
        (mem_closure_iff.1 hclosure') U hUopen homegaU
      exact (Set.disjoint_left.1 hdisj) hetaU hetaConn
    exact hnotclosure hclosure
  have homega_rev : omega ∈ frontier
      {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta y x} := by
    simpa only [connected_comm] using homega
  exact ⟨hinfinite x y hnotconn homega.1,
    hinfinite y x (fun hyx => hnotconn hyx.symm) homega_rev.1, hnotconn⟩

noncomputable def markReachableCount
    {V : Type*} (G : SimpleGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Finset V) (x : V) : Nat := by
  classical
  exact (A.filter fun y => (openSub G omega).Reachable x y).card

theorem allClustersEven_iff_mark_reachability
    {V : Type*} (G : SimpleGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Finset V) :
    AllClustersEven G omega A ↔
      ∀ x ∈ A, Even (markReachableCount G omega A x) := by
  classical
  constructor
  · intro h x hx
    have hh := h ((openSub G omega).connectedComponentMk x)
    simpa only [clusterMarkCount, markReachableCount,
      SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm] using hh
  · intro h C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ z =>
      by_cases hex : ∃ x ∈ A, (openSub G omega).Reachable z x
      · obtain ⟨x, hxA, hzx⟩ := hex
        have hcomp : (openSub G omega).connectedComponentMk z =
            (openSub G omega).connectedComponentMk x :=
          SimpleGraph.ConnectedComponent.sound hzx
        rw [hcomp]
        simpa only [clusterMarkCount, markReachableCount,
          SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm] using h x hxA
      · have hempty : A.filter
            (fun x => (openSub G omega).connectedComponentMk x =
              (openSub G omega).connectedComponentMk z) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.2
          intro x hx
          rw [Finset.mem_filter, SimpleGraph.ConnectedComponent.eq] at hx
          exact hex ⟨x, hx.1, hx.2.symm⟩
        simp only [clusterMarkCount, hempty, Finset.card_empty]
        norm_num

theorem allClustersEven_congr_of_mark_connectivity
    {V : Type*} (G : SimpleGraph V)
    (omega eta : ConfigSpace (Sym2 V)) (A : Finset V)
    (hconn : ∀ x ∈ A, ∀ y ∈ A,
      (openSub G omega).Reachable x y ↔ (openSub G eta).Reachable x y) :
    AllClustersEven G omega A ↔ AllClustersEven G eta A := by
  rw [allClustersEven_iff_mark_reachability,
    allClustersEven_iff_mark_reachability]
  constructor <;> intro h x hx
  · have heq : markReachableCount G omega A x =
        markReachableCount G eta A x := by
      unfold markReachableCount
      congr 1
      ext y
      simp only [Finset.mem_filter]
      exact and_congr_right fun hy => hconn x hx y hy
    rw [← heq]
    exact h x hx
  · have heq : markReachableCount G eta A x =
        markReachableCount G omega A x := by
      unfold markReachableCount
      congr 1
      ext y
      simp only [Finset.mem_filter]
      exact and_congr_right fun hy => (hconn x hx y hy).symm
    rw [← heq]
    exact h x hx

private noncomputable def connectivityStableNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) := by
  classical
  exact ⋂ x ∈ A, ⋂ y ∈ A,
    if Lattice.Connected d omega x y then
      {eta | Lattice.Connected d eta x y}
    else
      interior {eta | Lattice.Connected d eta x y}ᶜ

private theorem isOpen_connectivityStableNeighborhood_of_not_mem_frontier
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d)) :
    IsOpen (connectivityStableNeighborhood omega A) := by
  classical
  unfold connectivityStableNeighborhood
  apply isOpen_biInter_finset
  intro x hx
  apply isOpen_biInter_finset
  intro y hy
  split_ifs with hxy
  · exact isOpen_connectedEvent x y
  · exact isOpen_interior

private theorem mem_connectivityStableNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d))
    (hfront : ∀ x ∈ A, ∀ y ∈ A,
      omega ∉ frontier {eta : ConfigSpace (Sym2 (Site d)) |
        Lattice.Connected d eta x y}) :
    omega ∈ connectivityStableNeighborhood omega A := by
  classical
  unfold connectivityStableNeighborhood
  simp only [Set.mem_iInter]
  intro x hx y hy
  split_ifs with hxy
  · exact hxy
  · have hnot := hfront x hx y hy
    rw [← Set.mem_compl_iff, compl_frontier_eq_union_interior] at hnot
    rcases hnot with hint | hint
    · have hc : Lattice.Connected d omega x y := by
        have hm : omega ∈ {eta : ConfigSpace (Sym2 (Site d)) |
            Lattice.Connected d eta x y} :=
          (show interior {eta : ConfigSpace (Sym2 (Site d)) |
              Lattice.Connected d eta x y} ⊆
            {eta | Lattice.Connected d eta x y} from interior_subset) hint
        exact hm
      exact absurd hc hxy
    · exact hint

private theorem connectivityStableNeighborhood_connectivity
    (omega eta : ConfigSpace (Sym2 (Site d))) (A : Finset (Site d))
    (heta : eta ∈ connectivityStableNeighborhood omega A)
    {x y : Site d} (hx : x ∈ A) (hy : y ∈ A) :
    Connected d omega x y ↔ Connected d eta x y := by
  classical
  unfold connectivityStableNeighborhood at heta
  simp only [Set.mem_iInter] at heta
  have h := heta x hx y hy
  split_ifs at h with hxy
  · exact ⟨fun _ => h, fun _ => hxy⟩
  · exact ⟨fun hc => absurd hc hxy,
      fun hc => False.elim ((interior_subset h) hc)⟩



theorem frontier_allClustersEvenEvent_subset_atLeastTwoInfinite
    (A : Finset (Site d)) :
    frontier (allClustersEvenEvent (hypercubicLattice d) A) ⊆
      atLeastTwoInfinite d := by
  classical
  intro omega homega
  by_contra hnotmulti
  have hpairfront : ∀ x ∈ A, ∀ y ∈ A,
      omega ∉ frontier {eta : ConfigSpace (Sym2 (Site d)) |
        Connected d eta x y} := by
    intro x hx y hy hfront
    exact hnotmulti (distinctInfiniteClusterEvent_subset_atLeastTwoInfinite x y
      (frontier_connectedEvent_subset_distinctInfiniteClusterEvent x y hfront))
  let U := connectivityStableNeighborhood omega A
  have hUopen : IsOpen U :=
    isOpen_connectivityStableNeighborhood_of_not_mem_frontier omega A
  have homegaU : omega ∈ U :=
    mem_connectivityStableNeighborhood omega A hpairfront
  have hstable : ∀ eta ∈ U,
      AllClustersEven (hypercubicLattice d) omega A ↔
        AllClustersEven (hypercubicLattice d) eta A := by
    intro eta heta
    apply allClustersEven_congr_of_mark_connectivity
    intro x hx y hy
    simpa only [openSub, openSubgraph, FK.Connected] using
      connectivityStableNeighborhood_connectivity omega eta A heta hx hy
  by_cases heven : AllClustersEven (hypercubicLattice d) omega A
  · apply homega.2
    apply mem_interior_iff_mem_nhds.2
    exact mem_of_superset (hUopen.mem_nhds homegaU) fun eta heta =>
      (hstable eta heta).1 heven
  · have hcompl : omega ∈ interior
        (allClustersEvenEvent (hypercubicLattice d) A)ᶜ := by
      apply mem_interior_iff_mem_nhds.2
      apply mem_of_superset (hUopen.mem_nhds homegaU)
      intro eta heta
      exact fun hetaEven => heven ((hstable eta heta).2 hetaEven)
    have hnotclosure : omega ∉ closure
        (allClustersEvenEvent (hypercubicLattice d) A) := by
      rw [← Set.mem_compl_iff, ← interior_compl]
      exact hcompl
    exact hnotclosure homega.1



theorem measure_frontier_allClustersEvenEvent_eq_zero
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0)
    (A : Finset (Site d)) :
    (mu : Measure _) (frontier
      (allClustersEvenEvent (hypercubicLattice d) A)) = 0 :=
  measure_mono_null (frontier_allClustersEvenEvent_subset_atLeastTwoInfinite A)
    hunique

theorem measurable_markReachableCount_lattice
    (A : Finset (Site d)) (x : Site d) :
    Measurable (fun omega : ConfigSpace (Sym2 (Site d)) =>
      markReachableCount (hypercubicLattice d) omega A x) := by
  classical
  have heq : (fun omega : ConfigSpace (Sym2 (Site d)) =>
      markReachableCount (hypercubicLattice d) omega A x) =
      fun omega => ∑ y ∈ A,
        {eta : ConfigSpace (Sym2 (Site d)) |
          Lattice.Connected d eta x y}.indicator (fun _ => (1 : Nat)) omega := by
    funext omega
    simp only [markReachableCount, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hxy : Lattice.Connected d omega x y
    · have hxy' : (openSub (hypercubicLattice d) omega).Reachable x y := hxy
      simp [hxy, hxy']
    · have hxy' : ¬(openSub (hypercubicLattice d) omega).Reachable x y := hxy
      simp [hxy, hxy']
  rw [heq]
  apply Finset.measurable_sum
  intro y hy
  exact measurable_const.indicator (measurableSet_connected x y)

theorem measurableSet_allClustersEvenEvent (A : Finset (Site d)) :
    MeasurableSet (allClustersEvenEvent (hypercubicLattice d) A) := by
  classical
  have heq : allClustersEvenEvent (hypercubicLattice d) A =
      ⋂ x ∈ A, (fun omega : ConfigSpace (Sym2 (Site d)) =>
        markReachableCount (hypercubicLattice d) omega A x) ⁻¹'
          {n : Nat | Even n} := by
    ext omega
    simp only [allClustersEvenEvent, Set.mem_iInter, Set.mem_preimage,
      Set.mem_setOf_eq]
    exact allClustersEven_iff_mark_reachability (hypercubicLattice d) omega A
  rw [heq]
  apply Finset.measurableSet_biInter
  intro x hx
  exact MeasurableSet.preimage MeasurableSet.of_discrete
    (measurable_markReachableCount_lattice A x)

theorem WeakConvergesTo.tendsto_real_of_null_frontier
    {E : Type*} [Countable E]
    {mu : Nat → ProbabilityMeasure (ConfigSpace E)}
    {nu : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo mu nu) {A : Set (ConfigSpace E)}
    (hA : (nu : Measure _) (frontier A) = 0) :
    Tendsto (fun n => (mu n : Measure _).real A) atTop
      (nhds ((nu : Measure _).real A)) := by
  have hnn : Tendsto (fun n => mu n A) atTop (nhds (nu A)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto h
      (by
        have hz : (↑(nu (frontier A)) : ENNReal) = 0 := by
          rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
          exact hA
        exact ENNReal.coe_eq_zero.1 hz)
  have hcoe := (NNReal.continuous_coe.tendsto _).comp hnn
  simpa only [Function.comp_def, ProbabilityMeasure.coe_apply_eq_real] using hcoe

end StatMech.FrontierB
