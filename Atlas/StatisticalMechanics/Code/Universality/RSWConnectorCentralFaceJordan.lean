/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceFiniteGraph
import Code.Lattice.JordanEnclosureDuality











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section


def rlc_connectorCentralFacePlanarDomain {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorVertex n
  finV := inferInstance
  decV := inferInstance
  G := rlc_connectorCentralFaceClosureGraph gamma gamma'
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := fun _ _ hxy => hxy.1



theorem rlc_connectorCentralFace_faithfulDiscreteJordan {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    whc_FaithfulDiscreteJordan
      (rlc_connectorCentralFacePlanarDomain gamma gamma') :=
  jed_faithfulDiscreteJordan _



def rlc_connectorCentralFaceReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Set (Site 2) :=
  {z | ∃ hz : z ∈ rect (-2 * n) (2 * n) (-n) n,
    ConnectedWithin 2 (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨(rlc_connectorRightAnchor gamma : Site 2),
        (rlc_connectorRightAnchor gamma).2⟩ ⟨z, hz⟩}

theorem rlc_connectorCentralFaceReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorCentralFaceReachSet gamma gamma' rho).Finite := by
  apply (rect_finite (-2 * n) (2 * n) (-n) n).subset
  rintro z ⟨hz, _⟩
  exact hz

theorem rlc_connectorCentralFaceReachSet_extend {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {v w : Site 2}
    (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (hw : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_connectorCentralFaceAmbientConfig gamma gamma' rho s(v, w) = true) :
    w ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
  obtain ⟨hvBox, hvReach⟩ := hv
  refine ⟨hw, hvReach.trans ?_⟩
  exact (show (openSubgraphInduce 2
    (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)
    (rect (-2 * n) (2 * n) (-n) n)).Adj
      ⟨v, hvBox⟩ ⟨w, hw⟩ from ⟨hadj, hopen⟩).reachable



theorem rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {e : Sym2 (Site 2)}
    (hopen : rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true) :
    e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  unfold rlc_connectorCentralFaceAmbientConfig at hopen
  split at hopen
  · rename_i hrandom
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hrandom).1
  · rename_i hrandom
    split at hopen
    · rename_i htrace
      apply Finset.mem_union_right
      rw [rlc_connectorFourTraceEdges, Finset.mem_union]
      exact Or.inl htrace
    · simp at hopen



theorem rlc_openSub_centralFaceClosure_eq_openSubgraphInduce {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
        (rlc_connectorRestrictConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) =
      openSubgraphInduce 2
        (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)
        (rect (-2 * n) (2 * n) (-n) n) := by
  ext x y
  rw [FK.openSub_adj, openSubgraphInduce_adj]
  constructor
  · rintro ⟨⟨hadj, _hcarrier⟩, hopen⟩
    exact ⟨hadj, by simpa [rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen⟩
  · rintro ⟨hadj, hopen⟩
    have hcarrier := rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges
      gamma gamma' rho hopen
    exact ⟨⟨hadj, hcarrier⟩, by simpa [rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen⟩


theorem rlc_rightPathVertex_mem_centralFaceReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
  let z' : RlcConnectorVertex n :=
    ⟨z, rlc_rightPathVertex_mem_connectorBox gamma hz⟩
  have htrace := rlc_connectorTraceWiring_reachable_right gamma gamma'
    (rlc_connectorRightAnchor_onRight gamma)
      (show rlc_connectorOnRight gamma z' from hz)
  have hsource :
      (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
        (rlc_connectorRestrictConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))).Reachable
          (rlc_connectorRightAnchor gamma) z' := by
    rw [rlc_openSub_centralFaceClosure_ambient]
    exact htrace.mono le_sup_right
  refine ⟨z'.2, ?_⟩
  change (openSubgraphInduce 2
    (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)
    (rect (-2 * n) (2 * n) (-n) n)).Reachable
      ⟨(rlc_connectorRightAnchor gamma : Site 2),
        (rlc_connectorRightAnchor gamma).2⟩ ⟨z, z'.2⟩
  rw [← rlc_openSub_centralFaceClosure_eq_openSubgraphInduce]
  exact hsource



theorem rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma'.1) :
    z ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
  rintro ⟨hzBox, hzReach⟩
  let z' : RlcConnectorVertex n := ⟨z, hzBox⟩
  have hzSource :
      (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
        (rlc_connectorRestrictConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))).Reachable
          (rlc_connectorRightAnchor gamma) z' := by
    rw [rlc_openSub_centralFaceClosure_eq_openSubgraphInduce]
    exact hzReach
  have hleft := rlc_connectorTraceWiring_reachable_left gamma gamma'
    (show rlc_connectorOnLeft gamma' z' from hz)
      (rlc_connectorLeftAnchor_onLeft gamma')
  rw [rlc_openSub_centralFaceClosure_ambient] at hzSource
  have hanchors := hzSource.trans (hleft.mono
    (show rlc_connectorTraceWiring gamma gamma' ≤
      FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma' from le_sup_right))
  exact hno ((rlc_exists_connector_iff_traceAnchors gamma gamma'
    (FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho)).mpr
      hanchors)



theorem rlc_centralFaceReachSet_axis_boundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2
        (rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 := rlc_path_start_mem_vertices gamma.1
  have hyPath : y ∈ rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hxReach := rlc_rightPathVertex_mem_centralFaceReachSet
    gamma gamma' rho hxPath
  have hyNot := rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
    gamma gamma' rho hno hyPath
  have hx0 : x 0 = 0 := gamma.1.1.2.2
  have hy0 : y 0 = 0 := gamma'.1.2.1.2.2
  have hxx : x = ![0, x 1] := by
    ext i
    fin_cases i <;> simp [hx0]
  have hyy : y = ![0, y 1] := by
    ext i
    fin_cases i <;> simp [hy0]
  let w : (hypercubicLattice 2).Walk x y :=
    (sw_vertSeg 0 (x 1) (y 1)).copy hxx.symm hyy.symm
  obtain ⟨p, q, hpq, hpqEdge⟩ := rlc_walk_mem_edgeBoundary_edges
    (rlc_connectorCentralFaceReachSet gamma gamma' rho) w hxReach hyNot
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have hsupport (z : Site 2) (hz : z ∈ w.support) :
      ∃ t : Int, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![0, t] := by
    change z ∈ ((sw_vertSeg 0 (x 1) (y 1)).copy _ _).support at hz
    rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hz
    exact hz
  obtain ⟨tp, htp, rfl⟩ := hsupport p hpSupp
  obtain ⟨tq, htq, rfl⟩ := hsupport q hqSupp
  have hxRows : -n ≤ x 1 ∧ x 1 ≤ n := by
    have h := gamma.1.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have hyRows : -n ≤ y 1 ∧ y 1 ≤ n := by
    have h := gamma'.1.2.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have htpRows : -n ≤ tp ∧ tp ≤ n := by
    rw [Set.mem_uIcc] at htp
    rcases htp with htp | htp <;> omega
  have htqRows : -n ≤ tq ∧ tq ≤ n := by
    rw [Set.mem_uIcc] at htq
    rcases htq with htq | htq <;> omega
  refine ⟨![0, tp], ![0, tq], hpq, ?_, ?_, by simp, by simp⟩
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega




theorem rlc_centralFaceReachSet_verticalGap_boundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      ![0, t + 1] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)) := by
  classical
  let lower := (gamma.1.1 : Site 2) 1
  let upper := (gamma'.1.2.1 : Site 2) 1
  let S := rlc_connectorCentralFaceReachSet gamma gamma' rho
  have hlowerLt : lower < upper := by
    have hright := hposition.right_axis_strict
    have hleft := hposition.left_axis_strict
    dsimp [lower, upper]
    omega
  have hlowerPath : (![0, lower] : Site 2) ∈ rlc_pathVertices gamma.1 := by
    have haxis : (gamma.1.1 : Site 2) = ![0, lower] := by
      ext i
      fin_cases i <;> simp [lower, gamma.1.1.2.2]
    rw [← haxis]
    exact rlc_path_start_mem_vertices gamma.1
  have hupperPath : (![0, upper] : Site 2) ∈ rlc_pathVertices gamma'.1 := by
    have haxis : (gamma'.1.2.1 : Site 2) = ![0, upper] := by
      ext i
      fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
    rw [← haxis]
    exact rlc_connector_path_end_mem_vertices gamma'.1
  have hlower : (![0, lower] : Site 2) ∈ S :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho hlowerPath
  have hupper : (![0, upper] : Site 2) ∉ S :=
    rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
      gamma gamma' rho hno hupperPath
  let A : Finset Int := (Finset.Icc lower upper).filter
    (fun t => ![0, t] ∈ S)
  have hlowerA : lower ∈ A := by
    simp [A, hlower, le_of_lt hlowerLt]
  have hA : A.Nonempty := ⟨lower, hlowerA⟩
  let t := A.max' hA
  have htA : t ∈ A := A.max'_mem hA
  have htBounds : lower ≤ t ∧ t ≤ upper := by
    simpa [A] using (Finset.mem_filter.mp htA).1
  have htS : ![0, t] ∈ S := (Finset.mem_filter.mp htA).2
  have htlt : t < upper := by
    apply lt_of_le_of_ne htBounds.2
    intro h
    exact hupper (h ▸ htS)
  have hsuccNot : ![0, t + 1] ∉ S := by
    intro hsucc
    have hsuccA : t + 1 ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hsucc⟩
    have hmax := A.le_max' (t + 1) hsuccA
    change t + 1 ≤ t at hmax
    omega
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, htBounds.1, htlt, htS, hsuccNot,
    ⟨hadj, iff_of_true htS hsuccNot⟩⟩



theorem rlc_centralFaceReachSet_axis_anchored_boundaryCycle {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk u u),
      (p, q) ∈ edgeBoundary 2
          (rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨p, q, hpq, hpBox, hqBox, hp0, hq0⟩ :=
    rlc_centralFaceReachSet_axis_boundary_of_failure gamma gamma' rho hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho))
      T hT (degree_faceBoundaryGraph_even _) hfg
  exact ⟨p, q, f, g, u, c, hpq, hpBox, hqBox, hp0, hq0,
    hfg, hshared, hcyc, hedge⟩



theorem rlc_centralFaceReachSet_verticalGap_anchored_boundaryCycle {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (t : Int) (f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk u u),
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      ![0, t + 1] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g ∧
      sharedPrimalEdge f g = s((![0, t] : Site 2), ![0, t + 1]) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨t, htLower, htUpper, htIn, htOut, htBoundary⟩ :=
    rlc_centralFaceReachSet_verticalGap_boundary_of_failure
      gamma gamma' hposition rho hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces htBoundary.1
  have hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact htBoundary.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_connectorCentralFaceReachSet gamma gamma' rho)
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho))
      T hT (degree_faceBoundaryGraph_even _) hfg
  exact ⟨t, f, g, u, c, htLower, htUpper, htIn, htOut,
    hfg, hshared, hcyc, hedge⟩





theorem rlc_centralFaceReachSet_verticalGap_complementaryArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (t : Int) (f g : Site 2)
      (a : (faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk f g),
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      ![0, t + 1] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Adj f g ∧
      sharedPrimalEdge f g = s((![0, t] : Site 2), ![0, t + 1]) ∧
      s(f, g) ∉ a.edges := by
  obtain ⟨t, f, g, u, c, htLower, htUpper, htIn, htOut,
      hfg, hshared, hcyc, hedge⟩ :=
    rlc_centralFaceReachSet_verticalGap_anchored_boundaryCycle
      gamma gamma' hposition rho hno
  let B := faceBoundaryGraph
    (rlc_connectorCentralFaceReachSet gamma gamma' rho)
  have hreach : (B.deleteEdges {s(f, g)}).Reachable f g :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := B)).mpr ⟨u, c, hcyc, hedge⟩ |>.2
  obtain ⟨a, ha⟩ :=
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk (G := B)).mp hreach
  exact ⟨t, f, g, a, htLower, htUpper, htIn, htOut,
    hfg, hshared, ha⟩


def rlc_centralFaceContactSubwalk {H : SimpleGraph (Site 2)}
    {f g x y : Site 2} (a : H.Walk f g)
    (hx : x ∈ a.support) (hy : y ∈ a.support) : H.Walk x y :=
  (a.takeUntil x hx).reverse.append (a.takeUntil y hy)

theorem rlc_centralFaceContactSubwalk_edges_subset
    {H : SimpleGraph (Site 2)} {f g x y : Site 2} (a : H.Walk f g)
    (hx : x ∈ a.support) (hy : y ∈ a.support) :
    ∀ e ∈ (rlc_centralFaceContactSubwalk a hx hy).edges, e ∈ a.edges := by
  intro e he
  rw [rlc_centralFaceContactSubwalk,
    SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
    List.mem_append] at he
  rcases he with he | he
  · exact a.edges_takeUntil_subset hx (by simpa using he)
  · exact a.edges_takeUntil_subset hy he



theorem rlc_connectorCentralFaceReachSet_edgeBoundary_closed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)) :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho
  · have hw : w ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := hsplit.mp hv
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges
      gamma gamma' rho hopen
    have hwBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right v w)
    exact hw (rlc_connectorCentralFaceReachSet_extend gamma gamma' rho hv
      (by simpa [rlc_connectorBox] using hwBox) hadj hopen)
  · have hw : w ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges
      gamma gamma' rho hopen
    have hvBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right w v)
    exact hv (rlc_connectorCentralFaceReachSet_extend gamma gamma' rho hw
      (by simpa [rlc_connectorBox] using hvBox) hadj.symm hopen)



theorem rlc_connectorCentralFaceBoundary_le_openFaceDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_connectorCentralFaceReachSet_edgeBoundary_closed
    gamma gamma' rho hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed




def RlcCentralFaceBoundaryContactArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
      let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
      ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
        e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma'



def RlcCentralFaceWalkContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {f g : Site 2}
    (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk f g) : Prop :=
  ∃ (x y : Site 2) (hx : x ∈ a.support) (hy : y ∈ a.support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
      let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
      ∀ e ∈ (rlc_dualReflectOpenWalk eta
        ((rlc_centralFaceContactSubwalk a hx hy).mapLe hle)).edges,
        e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma'



theorem rlc_boundaryContactArc_of_walkContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {f g : Site 2}
    (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk f g)
    (hcontacts : RlcCentralFaceWalkContactSegment gamma gamma' rho a) :
    RlcCentralFaceBoundaryContactArc gamma gamma' rho := by
  obtain ⟨x, y, hx, hy, hxPath, hyPath, htarget⟩ := hcontacts
  exact ⟨x, y, rlc_centralFaceContactSubwalk a hx hy,
    hxPath, hyPath, htarget⟩



theorem rlc_centralFacePIMS_openWalk_of_reflected_walk {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {x y : Site 2}
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))).Walk x y)
    (hy : y ∈ rlc_pathVertices gamma'.1)
    (htarget : ∀ e ∈ c.edges,
      e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma') :
    ∃ (hxBox : x ∈ rect (-2 * n) (2 * n) (-n) n)
      (hyBox : y ∈ rect (-2 * n) (2 * n) (-n) n),
      Nonempty ((FK.openSub
        (rlc_connectorCentralFaceClosureGraph gamma gamma')
        (rlc_connectorCentralFacePIMSConfig gamma gamma' rho)).Walk
          ⟨x, hxBox⟩ ⟨y, hyBox⟩) := by
  have hyBox : y ∈ rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' hy
  have hsupp : ∀ z ∈ c.support,
      z ∈ rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · exact hyBox
    · simpa [rlc_connectorBox] using
        rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' (htarget e he) hze
  let cbox := c.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hsupp
  refine ⟨hsupp x c.start_mem_support, hyBox, ⟨cbox.transfer
    (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho)) ?_⟩⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      let hom := (SimpleGraph.Embedding.induce
        (G := openSubgraph 2 (rlc_dualReflectConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)))
        (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
      have hec : s((u : Site 2), (v : Site 2)) ∈ c.edges := by
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) cbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom cbox] at hmap
        simpa [hom, cbox] using hmap
      have hadj := c.adj_of_mem_edges hec
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      refine ⟨⟨hadj.1, htarget _ hec⟩, ?_⟩
      simpa [rlc_connectorCentralFacePIMSConfig,
        rlc_connectorRestrictConfig, Sym2.map_mk] using hadj.2



theorem rlc_centralFacePIMS_success_of_boundaryContactArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcCentralFaceBoundaryContactArc gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  obtain ⟨x, y, a, hx, hy, htarget⟩ := harc
  let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
  let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
  let c := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  obtain ⟨hxBox, hyBox, cfinite⟩ :=
    rlc_centralFacePIMS_openWalk_of_reflected_walk gamma gamma' rho c hy htarget
  exact ⟨⟨rlc_dualReflect x, hxBox⟩, ⟨rlc_dualReflect y, hyBox⟩,
    hx, hy, cfinite.some.reachable⟩

end

end StatMech.Universality
