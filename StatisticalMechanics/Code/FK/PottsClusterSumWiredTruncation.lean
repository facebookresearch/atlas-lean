/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumContinuity
import Code.FK.PottsClusterSumWiredWeakLimitIdentification









open Filter MeasureTheory Set Topology

namespace StatMech.FK

open Lattice Percolation

noncomputable section


def wiredTruncationEdge (d n : Nat)
    (omega : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) :=
  extendWiredEdge d n (boxRestrict d n omega)

theorem continuous_wiredTruncationEdge (d n : Nat) :
    Continuous (wiredTruncationEdge d n) := by
  exact continuous_of_discreteTopology.comp (continuous_boxRestrict d n)


theorem tendsto_wiredTruncationEdge
    {d : Nat} (omega : ConfigSpace (Sym2 (Site d))) :
    Tendsto (fun n => wiredTruncationEdge d n omega) atTop (nhds omega) := by
  apply tendsto_pi_nhds.2
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
      obtain ⟨N, hN⟩ := Percolation.finite_subset_box
        ({x, y} : Set (Site d))
        (Set.toFinite _)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ box d n := box_mono d hn (hN (by simp))
      have hy : y ∈ box d n := box_mono d hn (hN (by simp))
      let xb : boxVerts d n := ⟨x, hx⟩
      let yb : boxVerts d n := ⟨y, hy⟩
      change omega s(x, y) = wiredTruncationEdge d n omega s(x, y)
      rw [show s(x, y) = edgeIncl d n s(xb, yb) by
        simp [edgeIncl, xb, yb]]
      simp [wiredTruncationEdge, boxRestrict,
        extendWiredEdge_eq_of_range]



theorem boxOpen_adj_of_full
    {d n : Nat} (omega : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n}
    (hxy : (openSubgraph d omega).Adj (x : Site d) (y : Site d)) :
    (openSub (boxGraph d n) (boxRestrict d n omega)).Adj x y := by
  rw [openSubgraph_adj] at hxy
  rw [openSub_adj]
  constructor
  · simpa [boxGraph] using hxy.1
  · simpa [boxRestrict, edgeIncl] using hxy.2



theorem connToBdry_boxRestrict_of_connected_outside
    {d n : Nat} (hn : 1 <= n)
    (omega : ConfigSpace (Sym2 (Site d))) (x : boxVerts d n)
    {v : Site d} (hv : v ∉ box d n)
    (hreach : Lattice.Connected d omega (x : Site d) v) :
    IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n)
      (boxRestrict d n omega) x := by
  unfold Lattice.Connected at hreach
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  let OS := openSubgraph d omega
  let os := openSub (boxGraph d n) (boxRestrict d n omega)
  suffices H : ∀ w : Site d, Relation.ReflTransGen OS.Adj (x : Site d) w ->
      (IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n)
          (boxRestrict d n omega) x ∨
        ∃ y : boxVerts d n, (y : Site d) = w ∧ os.Reachable x y) by
    rcases H v hreach with hdone | ⟨y, hy, hxy⟩
    · exact hdone
    · exact absurd (hy ▸ y.2) hv
  intro w hw
  induction hw with
  | refl =>
      exact Or.inr ⟨x, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w huw hadj ih =>
      rcases ih with hdone | ⟨y, hy, hxy⟩
      · exact Or.inl hdone
      · subst hy
        by_cases hwbox : w ∈ box d n
        · let wb : boxVerts d n := ⟨w, hwbox⟩
          refine Or.inr ⟨wb, rfl, hxy.trans ?_⟩
          exact (boxOpen_adj_of_full omega hadj).reachable
        · left
          rw [openSubgraph_adj] at hadj
          exact ⟨y,
            ⟨y.2, notMem_box_pred_of_adj_outer hn y.2 hadj.1 hwbox⟩,
            hxy⟩





theorem cluster_wiredTruncationEdge_eq_of_finite
    {d n : Nat} (hd : 2 <= d) (hn : 1 <= n)
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hx : x ∈ box d n)
    (hfinite : (cluster d (wiredTruncationEdge d n omega) x).Finite) :
    cluster d (wiredTruncationEdge d n omega) x = cluster d omega x := by
  let xb : boxVerts d n := ⟨x, hx⟩
  have hnotBoundary : ¬ IsingFK.ConnToBdry
      (boxGraph d n) (boxBoundary d n) (boxRestrict d n omega) xb := by
    intro hconn
    exact (cluster_extendWiredEdge_infinite_of_connToBdry
      hd hn (boxRestrict d n omega) xb hconn) hfinite
  have horiginalSubset : cluster d omega x ⊆ box d n := by
    intro y hy
    by_contra hybox
    exact hnotBoundary (connToBdry_boxRestrict_of_connected_outside
      hn omega xb hybox (mem_cluster.mp hy))
  ext y
  constructor
  · intro hy
    have hybox : y ∈ box d n := by
      by_contra hyout
      exact hnotBoundary (connToBdry_of_extendWired_connected_outside
        hn (boxRestrict d n omega) xb hyout (mem_cluster.mp hy))
    let yb : boxVerts d n := ⟨y, hybox⟩
    rcases connToBdry_or_boxConnected_of_extendWired_connected
        hn (boxRestrict d n omega) xb yb (mem_cluster.mp hy) with
      hconn | hbox
    · exact (hnotBoundary hconn).elim
    · apply mem_cluster.mpr
      let hom : (openSub (boxGraph d n) (boxRestrict d n omega)) →g
          (openSubgraph d omega) :=
        { toFun := fun u => (u : Site d)
          map_rel' := by
            intro u v hadj
            rw [openSub_adj] at hadj
            rw [openSubgraph_adj]
            constructor
            · simpa [boxGraph] using hadj.1
            · simpa [boxRestrict, edgeIncl] using hadj.2 }
      simpa only [xb, yb] using hbox.map hom
  · intro hy
    let yb : boxVerts d n := ⟨y, horiginalSubset hy⟩
    obtain ⟨w⟩ := (mem_cluster.mp hy)
    have hsupp : ∀ z ∈ w.support, z ∈ box d n := by
      intro z hz
      apply horiginalSubset
      exact mem_cluster.mpr (w.takeUntil z hz).reachable
    have hbox : (openSub (boxGraph d n) (boxRestrict d n omega)).Reachable
        xb yb := by
      have hinduced : ((openSubgraph d omega).induce (box d n)).Reachable
          xb yb := ⟨w.induce (box d n) hsupp⟩
      let hom : ((openSubgraph d omega).induce (box d n)) →g
          (openSub (boxGraph d n) (boxRestrict d n omega)) :=
        { toFun := id
          map_rel' := by
            intro u v hadj
            exact boxOpen_adj_of_full omega hadj }
      exact hinduced.map hom
    exact mem_cluster.mpr
      (connected_extendWiredEdge_of_boxConnected
        (boxRestrict d n omega) hbox)



theorem cluster_wiredTruncationEdge_infinite_of_infinite
    {d n : Nat} (hd : 2 <= d) (hn : 1 <= n)
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hx : x ∈ box d n) (hinfinite : (cluster d omega x).Infinite) :
    (cluster d (wiredTruncationEdge d n omega) x).Infinite := by
  let xb : boxVerts d n := ⟨x, hx⟩
  obtain ⟨y, hy, hxy⟩ := (cluster_infinite_iff omega x).mp hinfinite n
  have hconn : IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n)
      (boxRestrict d n omega) xb :=
    connToBdry_boxRestrict_of_connected_outside hn omega xb hy hxy
  change (cluster d
    (extendWiredEdge d n (boxRestrict d n omega)) (xb : Site d)).Infinite
  exact cluster_extendWiredEdge_infinite_of_connToBdry
    hd hn (boxRestrict d n omega) xb hconn



theorem eventually_cluster_wiredTruncationEdge_eq_of_finite
    {d : Nat} (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfinite : (cluster d omega x).Finite) :
    ∀ᶠ n in atTop,
      cluster d (wiredTruncationEdge d n omega) x = cluster d omega x := by
  let E := clusterEvent d
    (StatMech.FrontierB.finiteClusterNeighborhood omega x hfinite :
      Set (Site d)) x (cluster d omega x)
  have hEclopen : IsClopen E :=
    StatMech.FrontierB.isClopen_finiteClusterEvent omega x hfinite
  have homega : omega ∈ E :=
    StatMech.FrontierB.clusterWithin_finiteClusterNeighborhood_eq_cluster
      omega x hfinite
  have heventually : ∀ᶠ n in atTop, wiredTruncationEdge d n omega ∈ E :=
    (tendsto_wiredTruncationEdge omega).eventually
      (hEclopen.isOpen.mem_nhds homega)
  filter_upwards [heventually] with n hn
  exact cluster_eq_of_mem_finiteClusterEvent
    omega (wiredTruncationEdge d n omega) x hfinite hn



theorem pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite
    {d q n : Nat} [NeZero q] (hd : 2 <= d) (hn : 1 <= n)
    (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q)
    (x : Site d) (hx : x ∈ box d n)
    (hfinite : (cluster d (wiredTruncationEdge d n omega) x).Finite) :
    pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega) label x =
      pottsClusterSumSpin boundaryColor omega label x := by
  have hcluster := cluster_wiredTruncationEdge_eq_of_finite
    hd hn omega x hx hfinite
  unfold pottsClusterSumSpin
  rw [hcluster]




theorem cluster_status_of_pottsClusterSumSpin_wiredTruncationEdge_ne
    {d q n : Nat} [NeZero q] (hd : 2 <= d) (hn : 1 <= n)
    (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q)
    (x : Site d) (hx : x ∈ box d n)
    (hne : pottsClusterSumSpin boundaryColor
        (wiredTruncationEdge d n omega) label x ≠
      pottsClusterSumSpin boundaryColor omega label x) :
    (cluster d (wiredTruncationEdge d n omega) x).Infinite ∧
      (cluster d omega x).Finite := by
  constructor
  · rcases (cluster d (wiredTruncationEdge d n omega) x).finite_or_infinite with
      hfinite | hinfinite
    · exact (hne (pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite
        hd hn boundaryColor omega label x hx hfinite)).elim
    · exact hinfinite
  · rcases (cluster d omega x).finite_or_infinite with hfinite | hinfinite
    · exact hfinite
    · have htruncated := cluster_wiredTruncationEdge_infinite_of_infinite
        hd hn omega x hx hinfinite
      exfalso
      apply hne
      rw [pottsClusterSumSpin_of_infinite boundaryColor
          (wiredTruncationEdge d n omega) label x htruncated,
        pottsClusterSumSpin_of_infinite boundaryColor omega label x hinfinite]



theorem eventually_cluster_wiredTruncationEdge_infinite
    {d : Nat} (hd : 2 <= d)
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinfinite : (cluster d omega x).Infinite) :
    ∀ᶠ n in atTop, (cluster d (wiredTruncationEdge d n omega) x).Infinite := by
  obtain ⟨N, hN⟩ := Percolation.finite_subset_box
    ({x} : Set (Site d)) (Set.toFinite _)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hNn : N <= n := le_max_left N 1 |>.trans hn
  have hn1 : 1 <= n := le_max_right N 1 |>.trans hn
  have hx : x ∈ box d n := box_mono d hNn (hN (by simp))
  let xb : boxVerts d n := ⟨x, hx⟩
  obtain ⟨y, hy, hxy⟩ := (cluster_infinite_iff omega x).mp hinfinite n
  have hconn : IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n)
      (boxRestrict d n omega) xb :=
    connToBdry_boxRestrict_of_connected_outside hn1 omega xb hy hxy
  change (cluster d
    (extendWiredEdge d n (boxRestrict d n omega)) (xb : Site d)).Infinite
  exact cluster_extendWiredEdge_infinite_of_connToBdry
    hd hn1 (boxRestrict d n omega) xb hconn



theorem eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q)
    (x : Site d) (hfinite : (cluster d omega x).Finite) :
    ∀ᶠ n in atTop,
      pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega)
          label x =
        pottsClusterSumSpin boundaryColor omega label x := by
  have hinput : Tendsto
      (fun n => (wiredTruncationEdge d n omega, label)) atTop
      (nhds (omega, label)) :=
    (tendsto_wiredTruncationEdge omega).prodMk_nhds tendsto_const_nhds
  have hspin :=
    (continuousAt_pottsClusterSumSpin_apply_of_finite boundaryColor
      (omega, label) x hfinite).tendsto.comp hinput
  have hsingleton :
      ({pottsClusterSumSpin boundaryColor omega label x} : Set (Fin q)) ∈
        nhds (pottsClusterSumSpin boundaryColor omega label x) :=
    (isOpen_discrete _).mem_nhds rfl
  filter_upwards [hspin hsingleton] with n hn
  simpa using hn



theorem eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_infinite
    {d q : Nat} [NeZero q] (hd : 2 <= d) (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q)
    (x : Site d) (hinfinite : (cluster d omega x).Infinite) :
    ∀ᶠ n in atTop,
      pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega)
          label x =
        pottsClusterSumSpin boundaryColor omega label x := by
  filter_upwards [eventually_cluster_wiredTruncationEdge_infinite
    hd omega x hinfinite] with n hn
  rw [pottsClusterSumSpin_of_infinite boundaryColor _ _ x hn,
    pottsClusterSumSpin_of_infinite boundaryColor _ _ x hinfinite]


theorem eventually_pottsClusterSumSpin_wiredTruncationEdge_eq
    {d q : Nat} [NeZero q] (hd : 2 <= d) (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q)
    (x : Site d) :
    ∀ᶠ n in atTop,
      pottsClusterSumSpin boundaryColor (wiredTruncationEdge d n omega)
          label x =
        pottsClusterSumSpin boundaryColor omega label x := by
  rcases (cluster d omega x).finite_or_infinite with hfinite | hinfinite
  · exact eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_finite
      boundaryColor omega label x hfinite
  · exact eventually_pottsClusterSumSpin_wiredTruncationEdge_eq_of_infinite
      hd boundaryColor omega label x hinfinite

end

end StatMech.FK
