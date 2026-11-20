/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumWeakLimitIdentification
import Code.Lattice.UniqueInfiniteComponent
import Code.IsingFK.HisingBoxClose
import Code.FK.InducedBC
import Code.FK.FreeDLRExtreme





open Filter MeasureTheory Set Topology

namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]






noncomputable def extendWiredEdge (d n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if h : e ∈ Set.range (edgeIncl d n) then omega h.choose else true

theorem measurable_extendWiredEdge (d n : Nat) :
    Measurable (extendWiredEdge d n) :=
  Measurable.of_discrete

theorem extendWiredEdge_eq_of_range
    {d : Nat} (n : Nat) (be : Sym2 (boxVerts d n))
    (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    extendWiredEdge d n omega (edgeIncl d n be) = omega be := by
  unfold extendWiredEdge
  have hmem : edgeIncl d n be ∈ Set.range (edgeIncl d n) := ⟨be, rfl⟩
  rw [dif_pos hmem, edgeIncl_injective d n hmem.choose_spec]

theorem extendWiredEdge_eq_true_of_not_range
    {d : Nat} (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {e : Sym2 (Site d)} (he : e ∉ Set.range (edgeIncl d n)) :
    extendWiredEdge d n omega e = true := by
  simp only [extendWiredEdge, dif_neg he]


theorem boxRestrict_extendWiredEdge (d n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    boxRestrict d n (extendWiredEdge d n omega) = omega := by
  funext e
  exact extendWiredEdge_eq_of_range n e omega



theorem extendWiredEdge_restrict_eq_extendEdge_restrict
    {d : Nat} (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (edges : Finset (Sym2 (Site d)))
    (hedges : ∀ e ∈ edges, e ∈ Set.range (edgeIncl d n)) :
    edges.restrict (extendWiredEdge d n omega) =
      edges.restrict (extendEdge d n omega) := by
  funext e
  obtain ⟨be, hbe⟩ := hedges e e.2
  change extendWiredEdge d n omega e = extendEdge d n omega e
  rw [← hbe, extendWiredEdge_eq_of_range, extendEdge_eq_of_range]


noncomputable def wiredOpenExteriorFiniteMeasure
    (d n : Nat) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  ⟨(wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure.map
      (extendWiredEdge d n),
    Measure.isProbabilityMeasure_map
      (measurable_extendWiredEdge d n).aemeasurable⟩



theorem eventually_wiredOpenExteriorFiniteMeasure_eq_wiredFiniteMeasure
    {d : Nat} {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : IsClopen A) :
    Filter.EventuallyEq atTop
      (fun k => ((wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq :
        ProbabilityMeasure _) : Measure _) A)
      (fun k => ((wiredFiniteMeasure d (phi k) hp hp1 hq :
        ProbabilityMeasure _) : Measure _) A) := by
  classical
  obtain ⟨F, hF⟩ := isClopen_dependsOn_finset A hA
  obtain ⟨N, t, ht⟩ := cdc_finset_in_box F
  filter_upwards [eventually_ge_atTop N] with k hk
  have hNphi : N ≤ phi k := hk.trans (hphi.id_le k)
  have hrange : ∀ e ∈ F, e ∈ Set.range (edgeIncl d (phi k)) := by
    intro e he
    rw [ht] at he
    obtain ⟨be, hbeMem, hbe⟩ := Finset.mem_image.mp he
    refine ⟨innerEdgeLE d hNphi be, ?_⟩
    rw [edgeIncl_innerEdgeLE, hbe]
  have hpre : extendWiredEdge d (phi k) ⁻¹' A =
      extendEdge d (phi k) ⁻¹' A := by
    ext omega
    exact hF _ _ (by
      intro e he
      obtain ⟨be, hbe⟩ := hrange e he
      rw [← hbe, extendWiredEdge_eq_of_range, extendEdge_eq_of_range])
  change Measure.map (extendWiredEdge d (phi k))
      (wiredFkPMF (boxGraph d (phi k)) (boxBoundary d (phi k))
        hp hp1 hq).toMeasure A =
    Measure.map (extendEdge d (phi k))
      (wiredFkPMF (boxGraph d (phi k)) (boxBoundary d (phi k))
        hp hp1 hq).toMeasure A
  rw [Measure.map_apply (measurable_extendWiredEdge d (phi k))
      hA.isOpen.measurableSet,
    Measure.map_apply (measurable_extendEdge d (phi k))
      hA.isOpen.measurableSet,
    hpre]

private theorem tendsto_probabilityMeasure_of_eventuallyEq_on_clopen
    {E : Type*} [Countable E]
    (mu nu : Nat -> ProbabilityMeasure (ConfigSpace E))
    (limit : ProbabilityMeasure (ConfigSpace E))
    (hmu : Tendsto mu atTop (nhds limit))
    (heq : ∀ A : Set (ConfigSpace E), IsClopen A ->
      Filter.EventuallyEq atTop (fun n => nu n A) (fun n => mu n A)) :
    Tendsto nu atTop (nhds limit) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro xi hxi
  obtain ⟨psi, hpsi, hnu⟩ := hxi.tendsto_subseq
  apply ProbabilityMeasure.ext_of_forall_isClopen
  intro A hA
  have hxiA := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hnu hA
  have hlimitA := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (hmu.comp hpsi.tendsto_atTop) hA
  have heqSub := (heq A hA).comp_tendsto hpsi.tendsto_atTop
  exact tendsto_nhds_unique hxiA (hlimitA.congr' heqSub.symm)



theorem tendsto_wiredOpenExteriorFiniteMeasure
    {d : Nat} {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hclosed : Tendsto (fun k => wiredFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit)) :
    Tendsto (fun k => wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit) := by
  apply tendsto_probabilityMeasure_of_eventuallyEq_on_clopen
    (fun k => wiredFiniteMeasure d (phi k) hp hp1 hq)
    (fun k => wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)
    edgeLimit hclosed
  intro A hA
  have hmeasure := eventually_wiredOpenExteriorFiniteMeasure_eq_wiredFiniteMeasure
    hp hp1 hq phi hphi A hA
  filter_upwards [hmeasure] with k hk
  apply ENNReal.coe_injective
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hk

private theorem exists_exterior_neighbor_of_boxBoundary
    {d n : Nat} (hn : 1 ≤ n) (y : boxVerts d n)
    (hy : boxBoundary d n y) :
    ∃ z : Site d, z ∈ exterior d n ∧
      (hypercubicLattice d).Adj (y : Site d) z := by
  rw [boxBoundary, mem_vertexBoundary] at hy
  simp only [mem_box, not_forall, not_le] at hy
  obtain ⟨i, hi⟩ := hy.2
  have habs : ((y : Site d) i).natAbs = n := by
    exact le_antisymm (hy.1 i) (by omega)
  by_cases hpos : 0 ≤ (y : Site d) i
  · let z : Site d := Function.update (y : Site d) i ((y : Site d) i + 1)
    refine ⟨z, ?_, ?_⟩
    · refine ⟨i, ?_⟩
      change n < (z i).natAbs
      simp only [z, Function.update_self]
      rw [
        Int.natAbs_add_of_nonneg hpos (by norm_num), habs]
      omega
    · rw [hypercubicLattice_adj]
      rw [Fintype.sum_eq_single i]
      · simp [z]
      · intro j hji
        simp [z, hji]
  · have hneg : (y : Site d) i < 0 := lt_of_not_ge hpos
    let z : Site d := Function.update (y : Site d) i ((y : Site d) i - 1)
    refine ⟨z, ?_, ?_⟩
    · refine ⟨i, ?_⟩
      change n < (z i).natAbs
      simp only [z, Function.update_self]
      rw [← Int.natAbs_neg]
      have hnonneg : 0 ≤ -((y : Site d) i) := by omega
      rw [show -((y : Site d) i - 1) = -((y : Site d) i) + 1 by ring,
        Int.natAbs_add_of_nonneg hnonneg (by norm_num), Int.natAbs_neg, habs]
      omega
    · rw [hypercubicLattice_adj]
      rw [Fintype.sum_eq_single i]
      · simp [z]
      · intro j hji
        simp [z, hji]

private theorem exterior_adj_extendWiredEdge
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : exterior d n}
    (hxy : ((hypercubicLattice d).induce (exterior d n)).Adj x y) :
    (openSubgraph d (extendWiredEdge d n omega)).Adj (x : Site d) (y : Site d) := by
  rw [SimpleGraph.induce_adj] at hxy
  rw [openSubgraph_adj]
  refine ⟨hxy, ?_⟩
  apply extendWiredEdge_eq_true_of_not_range n omega
  intro hrange
  obtain ⟨be, hbe⟩ := hrange
  have hbeEdge : be ∈ (boxGraph d n).edgeFinset :=
    boxEdge_mem n be (x : Site d) (y : Site d) hxy hbe
  have himage : s((x : Site d), (y : Site d)) ∈
      Finset.image (edgeIncl d n) (boxGraph d n).edgeFinset :=
    Finset.mem_image.mpr ⟨be, hbeEdge, hbe⟩
  have hxbox := (IsingFK.hbx_mem_image_edgeIncl_iff d n
    (x : Site d) (y : Site d)).mp himage |>.1
  have hxnot : (x : Site d) ∉ box d n := by
    intro hx
    obtain ⟨i, hi⟩ := x.2
    exact (not_lt_of_ge (hx i)) hi
  exact hxnot hxbox

private noncomputable def exteriorToExtendWiredOpenHom
    (d n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    (hypercubicLattice d).induce (exterior d n) →g
      openSubgraph d (extendWiredEdge d n omega) where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => exterior_adj_extendWiredEdge omega h

private theorem boxOpen_adj_extendWiredEdge
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (openSub (boxGraph d n) omega).Adj x y) :
    (openSubgraph d (extendWiredEdge d n omega)).Adj (x : Site d) (y : Site d) := by
  rw [openSub_adj] at hxy
  rw [openSubgraph_adj]
  constructor
  · simpa [boxGraph] using hxy.1
  · have heq : s((x : Site d), (y : Site d)) =
        edgeIncl d n s(x, y) := by
      simp [edgeIncl]
    rw [heq, extendWiredEdge_eq_of_range]
    exact hxy.2

private noncomputable def boxOpenToExtendWiredOpenHom
    (d n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    openSub (boxGraph d n) omega →g
      openSubgraph d (extendWiredEdge d n omega) where
  toFun := Subtype.val
  map_rel' := fun {_ _} h => boxOpen_adj_extendWiredEdge omega h

theorem connected_extendWiredEdge_of_boxConnected
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (openSub (boxGraph d n) omega).Reachable x y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) :=
  hxy.map (boxOpenToExtendWiredOpenHom d n omega)

private theorem boundary_adj_extendWiredEdge_exterior
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {y : boxVerts d n} {z : Site d}
    (hz : z ∈ exterior d n)
    (hyz : (hypercubicLattice d).Adj (y : Site d) z) :
    (openSubgraph d (extendWiredEdge d n omega)).Adj (y : Site d) z := by
  rw [openSubgraph_adj]
  refine ⟨hyz, ?_⟩
  apply extendWiredEdge_eq_true_of_not_range n omega
  intro hrange
  obtain ⟨be, hbe⟩ := hrange
  have hbeEdge : be ∈ (boxGraph d n).edgeFinset :=
    boxEdge_mem n be (y : Site d) z hyz hbe
  have himage : s((y : Site d), z) ∈
      Finset.image (edgeIncl d n) (boxGraph d n).edgeFinset :=
    Finset.mem_image.mpr ⟨be, hbeEdge, hbe⟩
  have hzbox := (IsingFK.hbx_mem_image_edgeIncl_iff d n
    (y : Site d) z).mp himage |>.2.1
  obtain ⟨i, hi⟩ := hz
  exact (not_lt_of_ge (hzbox i)) hi



theorem cluster_extendWiredEdge_infinite_of_connToBdry
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n)
    (hconn : IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x) :
    (cluster d (extendWiredEdge d n omega) (x : Site d)).Infinite := by
  obtain ⟨y, hybdry, hxy⟩ := hconn
  obtain ⟨z, hzext, hyz⟩ :=
    exists_exterior_neighbor_of_boxBoundary hn y hybdry
  have hxyFull : Lattice.Connected d (extendWiredEdge d n omega)
      (x : Site d) (y : Site d) :=
    connected_extendWiredEdge_of_boxConnected omega hxy
  have hyzFull : Lattice.Connected d (extendWiredEdge d n omega)
      (y : Site d) z :=
    (boundary_adj_extendWiredEdge_exterior omega hzext hyz).reachable
  apply (exterior_infinite n hd).mono
  intro w hw
  have hzwExterior := box_exterior_connected n hd z w hzext hw
  have hzwFull := hzwExterior.map (exteriorToExtendWiredOpenHom d n omega)
  exact hxyFull.trans (hyzFull.trans hzwFull)

private theorem boxOpen_of_extendWiredOpen
    {d n : Nat} (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (openSubgraph d (extendWiredEdge d n omega)).Adj
      (x : Site d) (y : Site d)) :
    (openSub (boxGraph d n) omega).Adj x y := by
  rw [openSubgraph_adj] at hxy
  rw [openSub_adj]
  constructor
  · simpa [boxGraph] using hxy.1
  · have heq : s((x : Site d), (y : Site d)) =
        edgeIncl d n s(x, y) := by
      simp [edgeIncl]
    rw [heq, extendWiredEdge_eq_of_range] at hxy
    exact hxy.2

theorem connToBdry_of_extendWired_connected_outside
    {d n : Nat} (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n)
    {v : Site d} (hv : v ∉ box d n)
    (hreach : (openSubgraph d (extendWiredEdge d n omega)).Reachable
      (x : Site d) v) :
    IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  let OS := openSubgraph d (extendWiredEdge d n omega)
  let os := openSub (boxGraph d n) omega
  suffices H : ∀ w : Site d, Relation.ReflTransGen OS.Adj (x : Site d) w ->
      (IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x ∨
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
          exact (boxOpen_of_extendWiredOpen omega hadj).reachable
        · left
          rw [openSubgraph_adj] at hadj
          exact ⟨y,
            ⟨y.2, notMem_box_pred_of_adj_outer hn y.2 hadj.1 hwbox⟩,
            hxy⟩

theorem connToBdry_or_boxConnected_of_extendWired_connected
    {d n : Nat} (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x y : boxVerts d n)
    (hreach : (openSubgraph d (extendWiredEdge d n omega)).Reachable
      (x : Site d) (y : Site d)) :
    IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x ∨
      (openSub (boxGraph d n) omega).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  let OS := openSubgraph d (extendWiredEdge d n omega)
  let os := openSub (boxGraph d n) omega
  have H : ∀ w : Site d, Relation.ReflTransGen OS.Adj (x : Site d) w ->
      (IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x ∨
        ∃ z : boxVerts d n, (z : Site d) = w ∧ os.Reachable x z) := by
    intro w hw
    induction hw with
    | refl => exact Or.inr ⟨x, rfl, SimpleGraph.Reachable.refl _⟩
    | @tail u w huw hadj ih =>
        rcases ih with hdone | ⟨z, hz, hxz⟩
        · exact Or.inl hdone
        · subst hz
          by_cases hwbox : w ∈ box d n
          · let wb : boxVerts d n := ⟨w, hwbox⟩
            refine Or.inr ⟨wb, rfl, hxz.trans ?_⟩
            exact (boxOpen_of_extendWiredOpen omega hadj).reachable
          · left
            rw [openSubgraph_adj] at hadj
            exact ⟨z,
              ⟨z.2, notMem_box_pred_of_adj_outer hn z.2 hadj.1 hwbox⟩,
              hxz⟩
  rcases H (y : Site d) hreach with hconn | ⟨z, hz, hxz⟩
  · exact Or.inl hconn
  · right
    have hzy : z = y := Subtype.ext hz
    simpa [hzy] using hxz



theorem cluster_extendWiredEdge_finite_of_not_connToBdry
    {d n : Nat} (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n)
    (hconn : ¬ IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x) :
    (cluster d (extendWiredEdge d n omega) (x : Site d)).Finite := by
  apply (box_finite d n).subset
  intro y hy
  by_contra hybox
  exact hconn (connToBdry_of_extendWired_connected_outside
    hn omega x hybox (mem_cluster.mp hy))



theorem cluster_extendWiredEdge_infinite_iff_connToBdry
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n) :
    (cluster d (extendWiredEdge d n omega) (x : Site d)).Infinite ↔
      IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x := by
  constructor
  · intro hinf
    by_contra hconn
    exact hinf (cluster_extendWiredEdge_finite_of_not_connToBdry
      hn omega x hconn)
  · exact cluster_extendWiredEdge_infinite_of_connToBdry hd hn omega x

private theorem boundary_connected_extendWiredEdge
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (x y : boxVerts d n) (hx : boxBoundary d n x) (hy : boxBoundary d n y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
  obtain ⟨zx, hzxExt, hxzx⟩ :=
    exists_exterior_neighbor_of_boxBoundary hn x hx
  obtain ⟨zy, hzyExt, hyzy⟩ :=
    exists_exterior_neighbor_of_boxBoundary hn y hy
  have hxzxFull : Lattice.Connected d (extendWiredEdge d n omega)
      (x : Site d) zx :=
    (boundary_adj_extendWiredEdge_exterior omega hzxExt hxzx).reachable
  have hzyyFull : Lattice.Connected d (extendWiredEdge d n omega)
      zy (y : Site d) :=
    (boundary_adj_extendWiredEdge_exterior omega hzyExt hyzy).reachable.symm
  have hzxzyExterior := box_exterior_connected n hd zx zy hzxExt hzyExt
  have hzxzyFull := hzxzyExterior.map (exteriorToExtendWiredOpenHom d n omega)
  exact hxzxFull.trans (hzxzyFull.trans hzyyFull)

private theorem wiredSub_adj_connected_extendWiredEdge
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega).Adj x y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
  rw [IsingFK.wiredSub, SimpleGraph.sup_adj] at hxy
  rcases hxy with hopen | hboundary
  · exact (boxOpen_adj_extendWiredEdge omega hopen).reachable
  · rw [boundaryCliqueGraph_adj] at hboundary
    exact boundary_connected_extendWiredEdge hd hn omega x y
      hboundary.2.1 hboundary.2.2



theorem wiredSub_reachable_connected_extendWiredEdge
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : boxVerts d n}
    (hxy : (IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega).Reachable x y) :
    Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
  unfold Lattice.Connected
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u v huv hadj ih =>
      exact ih.trans (wiredSub_adj_connected_extendWiredEdge hd hn omega hadj)



theorem extendWiredNonboundaryRepresentatives_law
    {d n q : Nat} [NeZero q] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (v0 : boxVerts d n) (hv0 : boxBoundary d n v0) :
    let W := IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega
    let c0 := W.connectedComponentMk v0
    let K := {C : W.ConnectedComponent // C ≠ c0}
    let r : K -> Site d := fun C => (C.1.out : boxVerts d n)
    Measure.map (fun label C =>
        pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (r C))
      (pottsIIDLabelMeasure d q) =
        Measure.infinitePi fun _ : K =>
          (PMF.uniformOfFintype (Fin q)).toMeasure := by
  dsimp only
  let W := IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega
  let c0 := W.connectedComponentMk v0
  let K := {C : W.ConnectedComponent // C ≠ c0}
  let r : K -> Site d := fun C => (C.1.out : boxVerts d n)
  have hnotconn (C : K) :
      ¬ IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega C.1.out := by
    intro hconn
    have heq := (IsingFK.connToBdry_iff_componentMk_eq
      (boxGraph d n) (boxBoundary d n) v0 hv0 omega C.1.out).mp hconn
    apply C.2
    calc
      C.1 = W.connectedComponentMk C.1.out := (Quot.out_eq C.1).symm
      _ = c0 := heq
  have hfinite : ∀ C : K,
      (cluster d (extendWiredEdge d n omega) (r C)).Finite := by
    intro C
    exact cluster_extendWiredEdge_finite_of_not_connToBdry hn omega C.1.out
      (hnotconn C)
  have hdistinct : ∀ C D : K, C ≠ D ->
      ¬ Lattice.Connected d (extendWiredEdge d n omega) (r C) (r D) := by
    intro C D hCD hfull
    rcases connToBdry_or_boxConnected_of_extendWired_connected
      hn omega C.1.out D.1.out hfull with hconn | hbox
    · exact (hnotconn C hconn).elim
    · apply hCD
      apply Subtype.ext
      have hle : openSub (boxGraph d n) omega ≤ W := by
        dsimp only [W]
        rw [IsingFK.wiredSub]
        exact le_sup_left
      calc
        C.1 = W.connectedComponentMk C.1.out := (Quot.out_eq C.1).symm
        _ = W.connectedComponentMk D.1.out :=
          SimpleGraph.ConnectedComponent.sound (hbox.mono hle)
        _ = D.1 := Quot.out_eq D.1
  exact pottsClusterSumSpin_representatives_law boundaryColor
    (extendWiredEdge d n omega) r hfinite hdistinct

namespace Wired

open IsingFK

variable (bdry : V -> Prop) [DecidablePred bdry]



abbrev CompatibleBoundarySpin {q : Nat} (b : Fin q)
    (omega : ConfigSpace (Sym2 V)) :=
  {sigma : V -> Fin q // ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma}

noncomputable instance compatibleBoundarySpinNonempty
    {q : Nat} (b : Fin q) (omega : ConfigSpace (Sym2 V)) :
    Nonempty (CompatibleBoundarySpin G bdry b omega) :=
  ⟨⟨fun _ => b, by
    constructor
    · intro x y hxy
      rfl
    · intro x hx
      rfl⟩⟩



noncomputable def compatibleBoundarySpinEquivPinnedWiredComponents
    {q : Nat} (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0) :
    CompatibleBoundarySpin G bdry b omega ≃
      {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
        tau ((wiredSub G bdry omega).connectedComponentMk v0) = b} := by
  let E : ((wiredSub G bdry omega).ConnectedComponent -> Fin q) ≃
      {sigma : V -> Fin q // ConstOnWired G bdry omega sigma} :=
    constOnWiredEquiv G bdry omega
  refine (Equiv.subtypeEquivRight (fun sigma =>
    constOnOpen_boundaryFixed_iff G bdry b omega sigma)).trans ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
  refine (E.subtypeEquiv ?_).symm
  intro tau
  show tau ((wiredSub G bdry omega).connectedComponentMk v0) = b ↔
    BoundaryFixed bdry b (E tau).1
  constructor
  · intro h x hx
    show tau ((wiredSub G bdry omega).connectedComponentMk x) = b
    rw [wiredSub_componentMk_eq_of_bdry G bdry hx hv0]
    exact h
  · intro h
    simpa [E, constOnWiredEquiv] using h v0 hv0

noncomputable instance wiredSubConnectedComponentDecidableEq
    (omega : ConfigSpace (Sym2 V)) :
    DecidableEq (wiredSub G bdry omega).ConnectedComponent :=
  Classical.decEq _



noncomputable def nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin
    {q : Nat} (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0) :
    ({C : (wiredSub G bdry omega).ConnectedComponent //
        C ≠ (wiredSub G bdry omega).connectedComponentMk v0} -> Fin q) ≃
      CompatibleBoundarySpin G bdry b omega :=
  by
    classical
    exact (pinnedFunEquiv
        ((wiredSub G bdry omega).connectedComponentMk v0) b).symm.trans
      (compatibleBoundarySpinEquivPinnedWiredComponents
        G bdry b omega v0 hv0).symm

@[simp]
theorem nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin_apply
    {q : Nat} (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0)
    (color : {C : (wiredSub G bdry omega).ConnectedComponent //
        C ≠ (wiredSub G bdry omega).connectedComponentMk v0} -> Fin q)
    (x : V) :
    (nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin
      G bdry b omega v0 hv0 color).1 x =
      if h : (wiredSub G bdry omega).connectedComponentMk x =
          (wiredSub G bdry omega).connectedComponentMk v0 then b
      else color ⟨(wiredSub G bdry omega).connectedComponentMk x, h⟩ := by
  rfl

noncomputable instance pinnedWiredComponentColoringNonempty
    {q : Nat} (b : Fin q) (omega : ConfigSpace (Sym2 V)) (v0 : V) :
    Nonempty
      {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
        tau ((wiredSub G bdry omega).connectedComponentMk v0) = b} :=
  ⟨⟨fun _ => b, rfl⟩⟩

private theorem uniformOfFintype_map_equiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [Nonempty alpha] [Nonempty beta] (e : alpha ≃ beta) :
    (PMF.uniformOfFintype alpha).map e = PMF.uniformOfFintype beta := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a hne
    rw [if_neg]
    intro heq
    apply hne
    apply e.injective
    simpa using heq.symm





noncomputable def conditionalClusterColorPMF
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V)) :
    PMF (V -> Fin q) :=
  (PMF.uniformOfFintype (CompatibleBoundarySpin G bdry b omega)).map Subtype.val

theorem conditionalClusterColorPMF_apply
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (sigma : V -> Fin q) :
    conditionalClusterColorPMF G bdry b omega sigma =
      if h : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then
        (Fintype.card (CompatibleBoundarySpin G bdry b omega) : ENNReal)⁻¹
      else 0 := by
  classical
  rw [conditionalClusterColorPMF, PMF.map_apply]
  by_cases h : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma
  · rw [dif_pos h, tsum_eq_single (⟨sigma, h⟩ : CompatibleBoundarySpin G bdry b omega)]
    · simp
    · intro tau hne
      rw [if_neg]
      intro heq
      apply hne
      exact Subtype.ext heq.symm
  · rw [dif_neg h]
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro tau htau
    rw [if_neg]
    intro heq
    apply h
    simpa [heq] using tau.2




theorem conditionalClusterColorPMF_eq_pinnedWiredComponents
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0) :
    conditionalClusterColorPMF G bdry b omega =
      (PMF.uniformOfFintype
        {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
          tau ((wiredSub G bdry omega).connectedComponentMk v0) = b}).map
        (fun tau x => tau.1
          ((wiredSub G bdry omega).connectedComponentMk x)) := by
  let E := compatibleBoundarySpinEquivPinnedWiredComponents
    G bdry b omega v0 hv0
  have huniform :
      (PMF.uniformOfFintype
        {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
          tau ((wiredSub G bdry omega).connectedComponentMk v0) = b}).map E.symm =
        PMF.uniformOfFintype (CompatibleBoundarySpin G bdry b omega) :=
    uniformOfFintype_map_equiv E.symm
  rw [conditionalClusterColorPMF, ← huniform, PMF.map_comp]
  congr 1

set_option maxHeartbeats 3000000 in



theorem extendWiredClusterSumSpin_law
    {d n q : Nat} [NeZero q] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (v0 : boxVerts d n) (hv0 : boxBoundary d n v0) :
    Measure.map (fun label (x : boxVerts d n) =>
        pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (x : Site d))
      (pottsIIDLabelMeasure d q) =
        (conditionalClusterColorPMF (boxGraph d n) (boxBoundary d n)
          boundaryColor omega).toMeasure := by
  let W := wiredSub (boxGraph d n) (boxBoundary d n) omega
  let c0 := W.connectedComponentMk v0
  let K := {C : W.ConnectedComponent // C ≠ c0}
  let r : K -> Site d := fun C => (C.1.out : boxVerts d n)
  let repColor : (Site d -> Fin q) -> K -> Fin q := fun label C =>
    pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega) label (r C)
  let E : (K -> Fin q) ≃ CompatibleBoundarySpin
      (boxGraph d n) (boxBoundary d n) boundaryColor omega :=
    nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin
      (boxGraph d n) (boxBoundary d n) boundaryColor omega v0 hv0
  have hrep := extendWiredNonboundaryRepresentatives_law
    hd hn boundaryColor omega v0 hv0
  change Measure.map repColor (pottsIIDLabelMeasure d q) =
      Measure.infinitePi fun _ : K =>
        (PMF.uniformOfFintype (Fin q)).toMeasure at hrep
  rw [Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform] at hrep
  have hfactor : (fun label (x : boxVerts d n) =>
      pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
        label (x : Site d)) = Subtype.val ∘ E ∘ repColor := by
    funext label x
    rw [Function.comp_apply, Function.comp_apply]
    rw [nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin_apply]
    by_cases hx : W.connectedComponentMk x = c0
    · rw [dif_pos hx]
      have hconn : ConnToBdry (boxGraph d n) (boxBoundary d n) omega x :=
        (connToBdry_iff_componentMk_eq
          (boxGraph d n) (boxBoundary d n) v0 hv0 omega x).mpr hx
      exact pottsClusterSumSpin_of_infinite boundaryColor
        (extendWiredEdge d n omega) label (x : Site d)
        (cluster_extendWiredEdge_infinite_of_connToBdry hd hn omega x hconn)
    · rw [dif_neg hx]
      let C : K := ⟨W.connectedComponentMk x, hx⟩
      change pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (x : Site d) =
        pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (r C)
      apply pottsClusterSumSpin_eq_of_connected boundaryColor
      apply wiredSub_reachable_connected_extendWiredEdge hd hn omega
      apply SimpleGraph.ConnectedComponent.exact
      change W.connectedComponentMk x = W.connectedComponentMk C.1.out
      exact (Quot.out_eq C.1).symm
  have hrepMeas : Measurable repColor := by
    exact measurable_pi_lambda _ fun C =>
      (measurable_pottsClusterSumSpin_apply boundaryColor (r C)).comp
        (measurable_const.prodMk measurable_id)
  have hpostMeas : Measurable (Subtype.val ∘ E) := Measurable.of_discrete
  rw [hfactor]
  have hcomp : Subtype.val ∘ E ∘ repColor =
      (Subtype.val ∘ E) ∘ repColor := rfl
  rw [hcomp, ← Measure.map_map hpostMeas hrepMeas, hrep]
  let uniformK := PMF.uniformOfFintype (K -> Fin q)
  have huniformE : uniformK.map E =
      PMF.uniformOfFintype
        (CompatibleBoundarySpin (boxGraph d n) (boxBoundary d n)
          boundaryColor omega) :=
    uniformOfFintype_map_equiv E
  have hpmf : uniformK.map (Subtype.val ∘ E) =
      conditionalClusterColorPMF (boxGraph d n) (boxBoundary d n)
        boundaryColor omega := by
    rw [← PMF.map_comp, huniformE]
    rfl
  change Measure.map (Subtype.val ∘ E) uniformK.toMeasure = _
  rw [PMF.toMeasure_map (Subtype.val ∘ E) uniformK Measurable.of_discrete,
    hpmf]

private theorem compatibleBoundarySpin_card_pos
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V)) :
    0 < Fintype.card (CompatibleBoundarySpin G bdry b omega) := by
  rw [Fintype.card_pos_iff]
  exact ⟨⟨fun _ => b, by
    constructor
    · intro x y hxy
      rfl
    · intro x hx
      rfl⟩⟩




theorem ivp_wiredJointProb_eq_wiredFkProb_div_card
    {q : Nat} [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (v0 : V) (hv0 : bdry v0)
    (sigma : V -> Fin q) (omega : ConfigSpace (Sym2 V)) :
    ivp_wiredJointProb G bdry b beta J (sigma, omega) =
      if ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then
        wiredFkProb G bdry (1 - Real.exp (-(beta * J))) (q : Real) omega /
          Fintype.card (CompatibleBoundarySpin G bdry b omega)
      else 0 := by
  classical
  let C : Nat := Fintype.card (CompatibleBoundarySpin G bdry b omega)
  have hC : (C : Real) ≠ 0 := by
    exact_mod_cast (compatibleBoundarySpin_card_pos G bdry b omega).ne'
  have hq : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_neZero q
  have hcount : ∀ eta : ConfigSpace (Sym2 V),
      1 ≤ numClustersBC G (boundaryCliqueGraph bdry) eta :=
    fun eta => one_le_numClustersBC G bdry v0 eta
  have hfk : wiredFkProb G bdry (1 - Real.exp (-(beta * J))) (q : Real) omega =
      edgeProduct G (1 - Real.exp (-(beta * J))) omega * C /
        esZWired G bdry q b (1 - Real.exp (-(beta * J))) := by
    rw [wiredFkProb_eq_bcProb]
    rw [← esWiredSecondMarginal_eq_bcProb G bdry b
      (1 - Real.exp (-(beta * J))) omega v0 hv0 (Nat.pos_of_neZero q) hcount]
    unfold esWiredSecondMarginal
    rw [esWeightWired_sum_spins]
    simp only [C, CompatibleBoundarySpin, Fintype.card_subtype]
  by_cases hcompat : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma
  · rw [if_pos hcompat, ivp_wiredJointProb, esWeightWired,
      if_pos hcompat.2, esWeight_eq_of_compatible]
    rw [if_pos ((compatible_iff_constOnOpen G sigma omega).mpr hcompat.1), hfk]
    change edgeProduct G (1 - Real.exp (-(beta * J))) omega /
        esZWired G bdry q b (1 - Real.exp (-(beta * J))) =
      (edgeProduct G (1 - Real.exp (-(beta * J))) omega * (C : Real) /
        esZWired G bdry q b (1 - Real.exp (-(beta * J)))) / (C : Real)
    field_simp
  · rw [if_neg hcompat, ivp_wiredJointProb, esWeightWired]
    by_cases hbf : BoundaryFixed bdry b sigma
    · rw [if_pos hbf, esWeight_eq_of_compatible]
      rw [if_neg (by
        intro hc
        exact hcompat ⟨(compatible_iff_constOnOpen G sigma omega).mp hc, hbf⟩)]
      simp
    · simp [hbf]



noncomputable def clusterColorJointPMF
    {q : Nat} [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    PMF ((V -> Fin q) × ConfigSpace (Sym2 V)) :=
  (wiredFkPMF G bdry hp hp1
    (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q)).bind fun omega =>
      (conditionalClusterColorPMF G bdry b omega).map fun sigma => (sigma, omega)



theorem clusterColorJointPMF_eq_ivp_wiredJointPMF
    {q : Nat} [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (v0 : V) (hv0 : bdry v0) :
    clusterColorJointPMF G bdry b beta J hp hp1 =
      ivp_wiredJointPMF G bdry b beta J hp.le := by
  classical
  ext z
  rcases z with ⟨sigma, omega⟩
  rw [clusterColorJointPMF, PMF.bind_apply, tsum_fintype,
    Finset.sum_eq_single omega]
  · simp only [PMF.map_apply, Prod.mk.injEq, and_true]
    have hpair : (∑' tau : V -> Fin q,
        if sigma = tau then conditionalClusterColorPMF G bdry b omega tau else 0) =
        conditionalClusterColorPMF G bdry b omega sigma := by
      rw [tsum_eq_single sigma]
      · simp
      · intro tau hne
        rw [if_neg]
        exact Ne.symm hne
    rw [hpair, conditionalClusterColorPMF_apply]
    simp only [ivp_wiredJointPMF, PMF.ofFintype_apply, wiredFkPMF,
      PMF.ofFintype_apply]
    rw [ivp_wiredJointProb_eq_wiredFkProb_div_card G bdry b beta J hp hp1
      v0 hv0 sigma omega]
    by_cases hcompat : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma
    · rw [dif_pos hcompat, if_pos hcompat]
      rw [ENNReal.ofReal_div_of_pos]
      · simp only [ENNReal.ofReal_natCast, div_eq_mul_inv]
      · exact_mod_cast compatibleBoundarySpin_card_pos G bdry b omega
    · simp [hcompat]
  · intro omega' _ hne
    simp [hne, Ne.symm hne]
  · simp



theorem wiredPottsJointFiniteMeasure_map_boxRestrict
    (d n q : Nat) [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    (wiredPottsJointFiniteMeasure d n q b beta J hp).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
          b beta J hp).toMeasure, inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (ivp_extendJoint d n q)
        (ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
          b beta J hp).toMeasure) = _
  rw [Measure.map_map (measurable_pottsBoxJointRestrict d n q)
    (ivp_measurable_extendJoint d n q)]
  have hleft : pottsBoxJointRestrict d n q ∘ ivp_extendJoint d n q = id := by
    funext z
    apply Prod.ext
    · funext x
      simp [pottsBoxJointRestrict, ivp_extendJoint, ivp_extendSpin, x.2]
    · funext e
      exact extendEdge_eq_of_range n e z.2
  rw [hleft, Measure.map_id]
  rfl



noncomputable def clusterColorJointFiniteMeasure
    (d n q : Nat) [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    ProbabilityMeasure (PottsJointConfig d q) :=
  ⟨(clusterColorJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp hp1).toMeasure.map (ivp_extendJoint d n q),
    Measure.isProbabilityMeasure_map
      (ivp_measurable_extendJoint d n q).aemeasurable⟩



theorem clusterColorJointFiniteMeasure_eq_wiredPottsJointFiniteMeasure
    (d n q : Nat) [NeZero q] (hd : 1 ≤ d) (hn : 1 ≤ n)
    (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    clusterColorJointFiniteMeasure d n q b beta J hp hp1 =
      wiredPottsJointFiniteMeasure d n q b beta J hp.le := by
  obtain ⟨v0, hv0⟩ := IsingFK.boxBoundary_nonempty d n hd hn
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (ivp_extendJoint d n q)
      (clusterColorJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp hp1).toMeasure =
    Measure.map (ivp_extendJoint d n q)
      (ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp.le).toMeasure
  rw [clusterColorJointPMF_eq_ivp_wiredJointPMF
    (boxGraph d n) (boxBoundary d n) b beta J hp hp1 v0 hv0]

end Wired

end StatMech.FK
