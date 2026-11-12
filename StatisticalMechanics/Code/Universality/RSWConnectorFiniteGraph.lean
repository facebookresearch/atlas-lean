/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.RSWGapSymmetry
import Code.Universality.RSWExtremalTraceContact
import Code.Universality.RSWExtremalSelectionObstruction
import Code.BeffaraDC.PlanarFKDuality
import Code.FK.MonoBC
import Code.FK.OffCentreDomination
import Code.FK.WeightedParameterMonotoneClosed
import Code.FrontierD.FKBoundarySingleMerge
import Code.Lattice.PeierlsHoleFreeBoundary



open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



private def rlc_connectorFlipHom {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))) →g
    ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))) where
  toFun x := ⟨rlc_flipX x,
    (rlc_connectorAllowed_mem_flipX_iff gamma gamma' x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [SimpleGraph.induce_adj] at hxy ⊢
    exact (rlc_adj_flipX x y).mp hxy


theorem rlc_connectorOriginRegionSet_mem_flipX {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegionSet gamma gamma') :
    rlc_flipX z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
  obtain ⟨hzAllowed, hoAllowed, hreach⟩ := hz
  have hreach' := hreach.map (rlc_connectorFlipHom gamma gamma')
  have horigin : rlc_flipX (origin 2) = origin 2 :=
    rlc_flipX_eq_self_of_zero rfl
  have hzAllowed' : rlc_flipX z ∈ rlc_connectorAllowed gamma gamma' :=
    (rlc_connectorAllowed_mem_flipX_iff gamma gamma' z).mp hzAllowed
  let o : {x // x ∈ (rlc_connectorAllowed gamma gamma' : Set (Site 2))} :=
    ⟨origin 2, hoAllowed⟩
  let z' : {x // x ∈ (rlc_connectorAllowed gamma gamma' : Set (Site 2))} :=
    ⟨rlc_flipX z, hzAllowed'⟩
  have hoMap : rlc_connectorFlipHom gamma gamma' o = o := by
    apply Subtype.ext
    exact horigin
  have hzMap : rlc_connectorFlipHom gamma gamma' ⟨z, hzAllowed⟩ = z' := by
    rfl
  have hreach'' : ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))).Reachable o z' := by
    rw [← hoMap, ← hzMap]
    exact hreach'
  exact ⟨hzAllowed', hoAllowed, hreach''⟩

theorem rlc_connectorOriginRegionSet_mem_flipX_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorOriginRegionSet gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
  constructor
  · exact rlc_connectorOriginRegionSet_mem_flipX gamma gamma'
  · intro hz
    simpa using rlc_connectorOriginRegionSet_mem_flipX gamma gamma' hz

theorem rlc_connectorOriginRegion_mem_flipX_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorOriginRegion gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorOriginRegion gamma gamma' := by
  simpa [rlc_connectorOriginRegion] using
    rlc_connectorOriginRegionSet_mem_flipX_iff gamma gamma' z



theorem rlc_connectorEdges_mem_map_flipX {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorEdges gamma gamma') :
    e.map rlc_flipX ∈ rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter] at he ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_edgesWithinFinset] at he ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := he.1
      exact ⟨rlc_flipX x, (rlc_connectorBox_mem_flipX_iff x).mp hx,
        rlc_flipX y, (rlc_connectorBox_mem_flipX_iff y).mp hy,
        by simp [Sym2.map_mk]⟩
    · obtain ⟨z, hzRegion, hzEdge⟩ := he.2
      refine ⟨rlc_flipX z,
        (rlc_connectorOriginRegion_mem_flipX_iff gamma gamma' z).mp hzRegion, ?_⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [Sym2.map_mk]
          rw [Sym2.mem_iff] at hzEdge ⊢
          rcases hzEdge with rfl | rfl <;> simp

theorem rlc_connectorEdges_mem_map_flipX_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : Sym2 (Site 2)) :
    e ∈ rlc_connectorEdges gamma gamma' ↔
      e.map rlc_flipX ∈ rlc_connectorEdges gamma gamma' := by
  constructor
  · exact rlc_connectorEdges_mem_map_flipX gamma gamma'
  · intro he
    have h := rlc_connectorEdges_mem_map_flipX gamma gamma' he
    simpa using h



theorem rlc_connectorReachSet_reflectedOpenDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      c.IsCycle := by
  obtain ⟨u, c, hcyc⟩ :=
    rlc_connectorReachSet_openFaceDualCircuit gamma gamma' omega hno
  exact ⟨u, rlc_dualReflectOpenWalk _ c,
    rlc_dualReflectOpenWalk_isCycle _ hcyc⟩


abbrev RlcConnectorVertex (n : Int) :=
  rect (-2 * n) (2 * n) (-n) n



def rlc_connectorFiniteGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2) ∧
      s((x : Site 2), (y : Site 2)) ∈ rlc_connectorEdges gamma gamma'
  symm := by
    intro x y hxy
    exact ⟨hxy.1.symm, by simpa [Sym2.eq_swap] using hxy.2⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorFiniteGraph_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorFiniteGraph gamma gamma').Adj :=
  Classical.decRel _



def rlc_connectorPlanarDomain {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorVertex n
  finV := inferInstance
  decV := inferInstance
  G := rlc_connectorFiniteGraph gamma gamma'
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    exact hxy.1



def rlc_connectorRestrictConfig {n : Int}
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  fun e => omega (e.map Subtype.val)



theorem rlc_openSub_connectorFiniteGraph_restrict_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorRestrictConfig omega) =
      openSubgraphInduce 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 * n) (2 * n) (-n) n) := by
  ext x y
  rw [FK.openSub_adj, openSubgraphInduce_adj, openSubgraph_adj]
  constructor
  · rintro ⟨⟨hadj, hedge⟩, hopen⟩
    refine ⟨hadj, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen
  · rintro ⟨hadj, hopen⟩
    have hedge : s((x : Site 2), (y : Site 2)) ∈
        rlc_connectorEdges gamma gamma' := by
      by_contra hedge
      simp [rlc_maskConfig, hedge] at hopen
    refine ⟨⟨hadj, hedge⟩, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen


def rlc_connectorOnRight {n : Int} (gamma : RlcRightDiagonalPath n)
    (x : RlcConnectorVertex n) : Prop :=
  (x : Site 2) ∈ rlc_pathVertices gamma.1


def rlc_connectorOnLeft {n : Int} (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorVertex n) : Prop :=
  (x : Site 2) ∈ rlc_pathVertices gamma'.1

noncomputable instance rlc_connectorOnRight_decidable {n : Int}
    (gamma : RlcRightDiagonalPath n) :
    DecidablePred (rlc_connectorOnRight gamma) := Classical.decPred _

noncomputable instance rlc_connectorOnLeft_decidable {n : Int}
    (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (rlc_connectorOnLeft gamma') := Classical.decPred _



def rlc_connectorSeparateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) :=
  Lattice.boundaryCliqueGraph (rlc_connectorOnRight gamma) ⊔
    Lattice.boundaryCliqueGraph (rlc_connectorOnLeft gamma')

noncomputable instance rlc_connectorSeparateWiring_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorSeparateWiring gamma gamma').Adj :=
  Classical.decRel _



def rlc_connectorTraceWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2) ∧
      s((x : Site 2), (y : Site 2)) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  symm := by
    intro x y hxy
    exact ⟨hxy.1.symm, by simpa [Sym2.eq_swap] using hxy.2⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorTraceWiring_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorTraceWiring gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_connectorTraceWiring_le_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorTraceWiring gamma gamma' ≤
      rlc_connectorSeparateWiring gamma gamma' := by
  intro x y hxy
  rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj]
  rcases Finset.mem_union.mp hxy.2 with hright | hleft
  · left
    rw [Lattice.boundaryCliqueGraph_adj]
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
    have hne : x ≠ y := fun h => hxy.1.ne (congrArg Subtype.val h)
    exact ⟨hne, hends.1, hends.2⟩
  · right
    rw [Lattice.boundaryCliqueGraph_adj]
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
    have hne : x ≠ y := fun h => hxy.1.ne (congrArg Subtype.val h)
    exact ⟨hne, hends.1, hends.2⟩



theorem rlc_connectorTraceWiring_reachable_right {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hx : rlc_connectorOnRight gamma x)
    (hy : rlc_connectorOnRight gamma y) :
    (rlc_connectorTraceWiring gamma gamma').Reachable x y := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hxW : (x : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (x : Site 2)).2 hx
  have hyW : (y : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (y : Site 2)).2 hy
  let wxy : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
    (W.takeUntil (x : Site 2) hxW).reverse.append
      (W.takeUntil (y : Site 2) hyW)
  have hwxyBox : ∀ z ∈ wxy.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
    intro z hz
    have hzW : z ∈ W.support := by
      dsimp only [wxy] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      rcases hz with hz | hz
      · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
      · exact W.support_takeUntil_subset_support hyW hz
    exact rlc_rightPathVertex_mem_connectorBox gamma
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzW)
  let wbox := wxy.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hwxyBox
  refine ⟨wbox.transfer (rlc_connectorTraceWiring gamma gamma') ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hexy : s((u : Site 2), (v : Site 2)) ∈ wxy.edges := by
        let hom := (SimpleGraph.Embedding.induce
          (G := hypercubicLattice 2)
          (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) wbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, by rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom wbox] at hmap
        simpa [hom, wbox] using hmap
      refine ⟨wxy.adj_of_mem_edges hexy, Finset.mem_union.mpr (Or.inl ?_)⟩
      exact rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1 (by
        dsimp only [wxy] at hexy
        simp only [SimpleGraph.Walk.edges_append,
          SimpleGraph.Walk.edges_reverse, List.mem_append,
          List.mem_reverse] at hexy
        rcases hexy with hexy | hexy
        · exact W.edges_takeUntil_subset hxW hexy
        · exact W.edges_takeUntil_subset hyW hexy)



theorem rlc_connectorTraceWiring_reachable_left {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hx : rlc_connectorOnLeft gamma' x)
    (hy : rlc_connectorOnLeft gamma' y) :
    (rlc_connectorTraceWiring gamma gamma').Reachable x y := by
  let W := rlc_ambientCrossingWalk gamma'.1
  have hxW : (x : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (x : Site 2)).2 hx
  have hyW : (y : Site 2) ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (y : Site 2)).2 hy
  let wxy : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
    (W.takeUntil (x : Site 2) hxW).reverse.append
      (W.takeUntil (y : Site 2) hyW)
  have hwxyBox : ∀ z ∈ wxy.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
    intro z hz
    have hzW : z ∈ W.support := by
      dsimp only [wxy] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      rcases hz with hz | hz
      · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
      · exact W.support_takeUntil_subset_support hyW hz
    exact rlc_leftPathVertex_mem_connectorBox gamma'
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).1 hzW)
  let wbox := wxy.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hwxyBox
  refine ⟨wbox.transfer (rlc_connectorTraceWiring gamma gamma') ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hexy : s((u : Site 2), (v : Site 2)) ∈ wxy.edges := by
        let hom := (SimpleGraph.Embedding.induce
          (G := hypercubicLattice 2)
          (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) wbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, by rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom wbox] at hmap
        simpa [hom, wbox] using hmap
      refine ⟨wxy.adj_of_mem_edges hexy, Finset.mem_union.mpr (Or.inr ?_)⟩
      exact rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1 (by
        dsimp only [wxy] at hexy
        simp only [SimpleGraph.Walk.edges_append,
          SimpleGraph.Walk.edges_reverse, List.mem_append,
          List.mem_reverse] at hexy
        rcases hexy with hexy | hexy
        · exact W.edges_takeUntil_subset hxW hexy
        · exact W.edges_takeUntil_subset hyW hexy)

private theorem rlc_reachable_of_step_reachable
    {V : Type*} {G K : SimpleGraph V}
    (hstep : ∀ {x y}, G.Adj x y → K.Reachable x y)
    {x y : V} (hxy : G.Reachable x y) : K.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons huv p ih => exact (hstep huv).trans ih



theorem rlc_connectorTraceWiring_reachable_iff_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (x y : RlcConnectorVertex n) :
    (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y ↔
      (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable x y := by
  constructor
  · exact Reachable.mono
      (sup_le_sup_left
        (rlc_connectorTraceWiring_le_separateWiring gamma gamma') H)
  · intro hxy
    apply rlc_reachable_of_step_reachable
      (G := H ⊔ rlc_connectorSeparateWiring gamma gamma')
      (K := H ⊔ rlc_connectorTraceWiring gamma gamma') ?_ hxy
    intro u v huv
    rcases huv with hH | hsep
    · exact (show (H ⊔ rlc_connectorTraceWiring gamma gamma').Adj u v
        from Or.inl hH).reachable
    · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
      rcases hsep with hright | hleft
      · rw [Lattice.boundaryCliqueGraph_adj] at hright
        exact (rlc_connectorTraceWiring_reachable_right gamma gamma'
          hright.2.1 hright.2.2).mono le_sup_right
      · rw [Lattice.boundaryCliqueGraph_adj] at hleft
        exact (rlc_connectorTraceWiring_reachable_left gamma gamma'
          hleft.2.1 hleft.2.2).mono le_sup_right



noncomputable def rlc_connectorTraceComponentEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n)) :
    (H ⊔ rlc_connectorTraceWiring gamma gamma').ConnectedComponent ≃
      (H ⊔ rlc_connectorSeparateWiring gamma gamma').ConnectedComponent := by
  let A := H ⊔ rlc_connectorTraceWiring gamma gamma'
  let B := H ⊔ rlc_connectorSeparateWiring gamma gamma'
  apply Equiv.ofBijective (fun C : A.ConnectedComponent =>
    B.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hB : B.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hA : A.Reachable C.out D.out :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring
        gamma gamma' H C.out D.out).mpr hB
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hA
  · intro D
    let C := A.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hA : A.Reachable C.out D.out :=
      ConnectedComponent.exact C.out_eq
    exact (rlc_connectorTraceWiring_reachable_iff_separateWiring
      gamma gamma' H C.out D.out).mp hA



theorem rlc_numClustersBC_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') tau =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') tau := by
  unfold FK.numClustersBC
  exact Nat.card_congr (rlc_connectorTraceComponentEquiv gamma gamma'
    (FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau))



theorem rlc_bcWeight_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q tau =
      FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau := by
  unfold FK.bcWeight
  rw [rlc_numClustersBC_traceWiring_eq_separateWiring]



theorem rlc_bcZ_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q =
      FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q := by
  unfold FK.bcZ
  apply Finset.sum_congr rfl
  intro tau _
  exact rlc_bcWeight_traceWiring_eq_separateWiring gamma gamma' p q tau



theorem rlc_bcProb_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q tau =
      FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau := by
  unfold FK.bcProb
  rw [rlc_bcWeight_traceWiring_eq_separateWiring,
    rlc_bcZ_traceWiring_eq_separateWiring]



theorem rlc_bcEventMass_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q A =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A := by
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_traceWiring_eq_separateWiring]



def rlc_connectorAugmentedPlanarDomain {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorVertex n
  finV := inferInstance
  decV := inferInstance
  G := rlc_connectorFiniteGraph gamma gamma' ⊔
    rlc_connectorTraceWiring gamma gamma'
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact hxy.1
    · exact hxy.1




theorem rlc_connectorFiniteGraph_adj_not_traceWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
    ¬ (rlc_connectorTraceWiring gamma gamma').Adj x y := by
  intro htrace
  rcases Finset.mem_union.mp htrace.2 with hright | hleft
  · exact (Finset.disjoint_left.mp
      (rlc_rightPathEdges_disjoint_connector gamma gamma'))
        hright hxy.2
  · exact (Finset.disjoint_left.mp
      (rlc_leftPathEdges_disjoint_connector gamma gamma'))
        hleft hxy.2



def rlc_connectorForceTraceConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  fun e => if e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset
    then true else tau e



theorem rlc_openSub_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  simp only [FK.openSub_adj, rlc_connectorAugmentedPlanarDomain,
    SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hfinite | htrace, hopen⟩
    · left
      refine ⟨hfinite, ?_⟩
      have hnot : s(x, y) ∉
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        intro hmem
        exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma'
          hfinite ((SimpleGraph.mem_edgeSet
            (rlc_connectorTraceWiring gamma gamma')).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
      change (if s(x, y) ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
          then true else tau s(x, y)) = true at hopen
      rw [if_neg hnot] at hopen
      exact hopen
    · exact Or.inr htrace
  · rintro (⟨hfinite, hopen⟩ | htrace)
    · refine ⟨Or.inl hfinite, ?_⟩
      have hnot : s(x, y) ∉
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        intro hmem
        exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma'
          hfinite ((SimpleGraph.mem_edgeSet
            (rlc_connectorTraceWiring gamma gamma')).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
      change (if s(x, y) ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
          then true else tau s(x, y)) = true
      rw [if_neg hnot]
      exact hopen
    · refine ⟨Or.inr htrace, ?_⟩
      have hmem : s(x, y) ∈
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        exact SimpleGraph.mem_edgeFinset.mpr
          ((SimpleGraph.mem_edgeSet
            (rlc_connectorTraceWiring gamma gamma')).mpr htrace)
      change (if s(x, y) ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
          then true else tau s(x, y)) = true
      rw [if_pos hmem]



theorem rlc_numClusters_augmented_forceTrace_eq_traceBC {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClusters (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') tau := by
  let A := FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
    (rlc_connectorForceTraceConfig gamma gamma' tau)
  let B := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
    rlc_connectorTraceWiring gamma gamma'
  have hAB : A = B := rlc_openSub_augmented_forceTrace gamma gamma' tau
  have htypes : A.ConnectedComponent = B.ConnectedComponent :=
    congrArg (fun H : SimpleGraph (RlcConnectorVertex n) =>
      H.ConnectedComponent) hAB
  unfold FK.numClusters FK.numClustersBC
  calc
    Fintype.card A.ConnectedComponent = Nat.card A.ConnectedComponent :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card B.ConnectedComponent :=
      Nat.card_congr (Equiv.cast htypes)





theorem rlc_connectorForced_clusterEuler {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
    let K := FK.openSub P.G
      (rlc_connectorForceTraceConfig gamma gamma' tau)
    Nat.card P.V +
        Nat.card (BeffaraDC.pfdClosedDual P K).ConnectedComponent =
      K.edgeSet.ncard +
        FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') tau + 1 := by
  dsimp only
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma' tau)
  have heuler := BeffaraDC.pfd_clusterEuler P K
    (FK.openSub_le P.G (rlc_connectorForceTraceConfig gamma gamma' tau))
  have hk : Nat.card K.ConnectedComponent =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') tau := by
    calc
      Nat.card K.ConnectedComponent = Fintype.card K.ConnectedComponent :=
        Nat.card_eq_fintype_card
      _ = FK.numClusters P.G
          (rlc_connectorForceTraceConfig gamma gamma' tau) := rfl
      _ = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorTraceWiring gamma gamma') tau :=
        rlc_numClusters_augmented_forceTrace_eq_traceBC gamma gamma' tau
      _ = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') tau :=
        rlc_numClustersBC_traceWiring_eq_separateWiring gamma gamma' tau
  simpa only [P, K, hk] using heuler




theorem rlc_edgeProduct_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.edgeProduct (rlc_connectorAugmentedPlanarDomain gamma gamma').G p
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.edgeProduct (rlc_connectorFiniteGraph gamma gamma') p tau := by
  classical
  let G := rlc_connectorFiniteGraph gamma gamma'
  let T := rlc_connectorTraceWiring gamma gamma'
  have hd : Disjoint G.edgeFinset T.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heG heT
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hG : G.Adj x y := (SimpleGraph.mem_edgeSet G).mp
          (SimpleGraph.mem_edgeFinset.mp heG)
        have hT : T.Adj x y := (SimpleGraph.mem_edgeSet T).mp
          (SimpleGraph.mem_edgeFinset.mp heT)
        exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma' hG hT
  have hGprod :
      (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) =
        ∏ e ∈ G.edgeFinset, if tau e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e heG
    have hnot : e ∉ T.edgeFinset := Finset.disjoint_left.mp hd heG
    simp [rlc_connectorForceTraceConfig, T, hnot]
  have hTprod :
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) = p ^ T.edgeFinset.card := by
    calc
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) = ∏ _e ∈ T.edgeFinset, p := by
        apply Finset.prod_congr rfl
        intro e heT
        have hforce : rlc_connectorForceTraceConfig gamma gamma' tau e = true := by
          simp [rlc_connectorForceTraceConfig, T, heT]
        simp only [hforce, if_true]
      _ = p ^ T.edgeFinset.card := by simp
  unfold FK.edgeProduct
  have hEdges :
      (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset =
        G.edgeFinset ∪ T.edgeFinset := by
    simp [rlc_connectorAugmentedPlanarDomain, G, T]
  rw [hEdges]
  calc
    (∏ e ∈ G.edgeFinset ∪ T.edgeFinset,
        if rlc_connectorForceTraceConfig gamma gamma' tau e
          then p else 1 - p) =
        (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) *
        ∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p := Finset.prod_union hd
    _ = (∏ e ∈ G.edgeFinset, if tau e then p else 1 - p) *
        p ^ T.edgeFinset.card := by rw [hGprod, hTprod]
    _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        ∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
          if tau e then p else 1 - p := by simp only [G, T, mul_comm]



theorem rlc_fkWeight_augmented_forceTrace_eq_separateBC {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.fkWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G p q
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q tau := by
  unfold FK.fkWeight FK.bcWeight
  rw [rlc_edgeProduct_augmented_forceTrace,
    rlc_numClusters_augmented_forceTrace_eq_traceBC,
    rlc_numClustersBC_traceWiring_eq_separateWiring]
  ring



theorem rlc_connectorForced_weight_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
    let forced := rlc_connectorForceTraceConfig gamma gamma' tau
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q tau *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          BeffaraDC.pfdDualWeight P (BeffaraDC.dualParam p q) q
            (FK.openSub P.G forced) := by
  dsimp only
  rw [← rlc_fkWeight_augmented_forceTrace_eq_separateBC]
  exact BeffaraDC.pfd_fkWeight_duality
    (rlc_connectorAugmentedPlanarDomain gamma gamma')
    (rlc_connectorForceTraceConfig gamma gamma' tau) hp hp1 hq



noncomputable def rlc_connectorForcedDualZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  ∑ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' tau))


noncomputable def rlc_connectorForcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Real :=
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' tau)) /
    rlc_connectorForcedDualZ gamma gamma' p q

theorem rlc_connectorForcedDualZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_connectorForcedDualZ gamma gamma' p q := by
  unfold rlc_connectorForcedDualZ
  exact Finset.sum_pos
    (fun tau _ => BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)) hp hp1 hq)
    Finset.univ_nonempty



theorem rlc_connectorForced_partition_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          rlc_connectorForcedDualZ gamma gamma'
            (BeffaraDC.dualParam p q) q := by
  dsimp only
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  let t : Real := p ^
    (rlc_connectorTraceWiring gamma gamma').edgeFinset.card
  let A : Real := q ^ (P.G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
      q ^ Nat.card P.V
  unfold FK.bcZ rlc_connectorForcedDualZ
  calc
    t * (∑ tau, FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau) * A =
      ∑ tau, t * FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau * A := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ tau, B * BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' tau)) := by
      apply Finset.sum_congr rfl
      intro tau _
      exact rlc_connectorForced_weight_duality gamma gamma' tau hp hp1 hq
    _ = B * ∑ tau, BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' tau)) := by
      rw [Finset.mul_sum]




theorem rlc_bcProb_separate_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q tau =
      rlc_connectorForcedDualProb gamma gamma'
        (BeffaraDC.dualParam p q) q tau := by
  have hps0 : 0 < BeffaraDC.dualParam p q :=
    BeffaraDC.dualParam_pos hp hp1 hq
  have hps1 : BeffaraDC.dualParam p q < 1 :=
    BeffaraDC.dualParam_lt_one hp hp1 hq
  have hZp : FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') p q ≠ 0 :=
    (FK.bcZ_pos (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') hp hp1 hq).ne'
  have hZd : rlc_connectorForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q ≠ 0 :=
    (rlc_connectorForcedDualZ_pos gamma gamma' hps0 hps1 hq).ne'
  let C : Real :=
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
      q ^ ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card *
      q ^ Nat.card (rlc_connectorAugmentedPlanarDomain gamma gamma').V
  let wp := FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma') p q tau
  let wd := BeffaraDC.pfdDualWeight
    (rlc_connectorAugmentedPlanarDomain gamma gamma')
    (BeffaraDC.dualParam p q) q
    (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
      (rlc_connectorForceTraceConfig gamma gamma' tau))
  have hC : 0 < C := mul_pos (pow_pos hp _) (pow_pos hq _)
  have hB : 0 < B := by
    have hden : 0 < 1 - BeffaraDC.dualParam p q := by linarith
    exact mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)
  have hw : wp * C = B * wd := by
    have h := rlc_connectorForced_weight_duality
      gamma gamma' tau hp hp1 hq
    dsimp only at h
    dsimp only [wp, wd, C, B]
    nlinarith
  have hZ : FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q * C =
      B * rlc_connectorForcedDualZ gamma gamma'
        (BeffaraDC.dualParam p q) q := by
    have h := rlc_connectorForced_partition_duality
      gamma gamma' hp hp1 hq
    dsimp only at h
    dsimp only [C, B]
    nlinarith
  have hcross : wp * rlc_connectorForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q =
      wd * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q := by
    apply mul_left_cancel₀ hB.ne'
    calc
      B * (wp * rlc_connectorForcedDualZ gamma gamma'
          (BeffaraDC.dualParam p q) q) =
          wp * (B * rlc_connectorForcedDualZ gamma gamma'
            (BeffaraDC.dualParam p q) q) := by ring
      _ = wp * (FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q * C) := by rw [hZ]
      _ = (wp * C) * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q := by ring
      _ = (B * wd) * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q := by rw [hw]
      _ = B * (wd * FK.bcZ (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q) := by ring
  unfold FK.bcProb rlc_connectorForcedDualProb
  apply (div_eq_div_iff hZp hZd).2
  simpa only [wp, wd] using hcross



noncomputable def rlc_connectorForcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) : Real :=
  ∑ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    A.indicator (fun _ => (1 : Real)) tau *
      rlc_connectorForcedDualProb gamma gamma' p q tau



theorem rlc_connectorEdge_exists_lift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorEdges gamma gamma') :
    ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
  rw [rlc_connectorEdges, Finset.mem_filter, mem_edgesWithinFinset] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he.1
  let xf : RlcConnectorVertex n := ⟨x, by
    simpa [RlcConnectorVertex, rlc_connectorBox] using hx⟩
  let yf : RlcConnectorVertex n := ⟨y, by
    simpa [RlcConnectorVertex, rlc_connectorBox] using hy⟩
  exact ⟨s(xf, yf), by simp [Sym2.map_mk, xf, yf]⟩

noncomputable def rlc_connectorEdgeLift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : Sym2 (Site 2)) (he : e ∈ rlc_connectorEdges gamma gamma') :
    Sym2 (RlcConnectorVertex n) :=
  Classical.choose (rlc_connectorEdge_exists_lift gamma gamma' he)

@[simp] theorem rlc_connectorEdgeLift_map {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : Sym2 (Site 2)) (he : e ∈ rlc_connectorEdges gamma gamma') :
    (rlc_connectorEdgeLift gamma gamma' e he).map Subtype.val = e :=
  Classical.choose_spec (rlc_connectorEdge_exists_lift gamma gamma' he)



noncomputable def rlc_connectorAmbientMixedConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if he : e ∈ rlc_connectorEdges gamma gamma' then
      tau (rlc_connectorEdgeLift gamma gamma' e he)
    else if e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then
      true
    else false

@[simp] theorem rlc_connectorAmbientMixedConfig_connectorEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorEdges gamma gamma') :
    rlc_connectorAmbientMixedConfig gamma gamma' tau e =
      tau (rlc_connectorEdgeLift gamma gamma' e he) := by
  simp [rlc_connectorAmbientMixedConfig, he]

@[simp] theorem rlc_connectorAmbientMixedConfig_traceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorAmbientMixedConfig gamma gamma' tau e = true := by
  have hnot : e ∉ rlc_connectorEdges gamma gamma' := by
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma') hright
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma') hleft
  simp [rlc_connectorAmbientMixedConfig, hnot, he]




noncomputable def rlc_connectorPIMSExteriorPreimages {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  (rlc_connectorEdges gamma gamma').image rlc_pimsEdgeEquiv \
    (rlc_connectorEdges gamma gamma' ∪
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1))

theorem rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_pimsEdgeEquiv e ∈
      rlc_connectorPIMSExteriorPreimages gamma gamma' := by
  rw [rlc_connectorPIMSExteriorPreimages, Finset.mem_sdiff]
  refine ⟨Finset.mem_image.mpr ⟨e, htarget, rfl⟩, ?_⟩
  rw [Finset.mem_union]
  exact not_or_intro hsource htrace



noncomputable def rlc_connectorAmbientCollaredConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if he : e ∈ rlc_connectorEdges gamma gamma' then
      tau (rlc_connectorEdgeLift gamma gamma' e he)
    else if e ∈
        (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_connectorPIMSExteriorPreimages gamma gamma' then
      true
    else false

@[simp] theorem rlc_connectorAmbientCollaredConfig_connectorEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorEdges gamma gamma') :
    rlc_connectorAmbientCollaredConfig gamma gamma' tau e =
      tau (rlc_connectorEdgeLift gamma gamma' e he) := by
  simp [rlc_connectorAmbientCollaredConfig, he]

@[simp] theorem rlc_connectorAmbientCollaredConfig_traceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorAmbientCollaredConfig gamma gamma' tau e = true := by
  have hnot : e ∉ rlc_connectorEdges gamma gamma' := by
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma') hright
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma') hleft
  have hforced : e ∈
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_connectorPIMSExteriorPreimages gamma gamma' :=
    Finset.mem_union_left _ he
  rw [rlc_connectorAmbientCollaredConfig, dif_neg hnot, if_pos hforced]

@[simp] theorem rlc_connectorAmbientCollaredConfig_collarEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorPIMSExteriorPreimages gamma gamma') :
    rlc_connectorAmbientCollaredConfig gamma gamma' tau e = true := by
  have hnotUnion : e ∉ rlc_connectorEdges gamma gamma' ∪
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :=
    (Finset.mem_sdiff.mp he).2
  have hnot : e ∉ rlc_connectorEdges gamma gamma' :=
    fun h => hnotUnion (Finset.mem_union_left _ h)
  have hforced : e ∈
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_connectorPIMSExteriorPreimages gamma gamma' :=
    Finset.mem_union_right _ he
  rw [rlc_connectorAmbientCollaredConfig, dif_neg hnot, if_pos hforced]

private theorem rlc_sym2Map_subtypeVal_injective {n : Int} :
    Function.Injective
      (Sym2.map (Subtype.val : RlcConnectorVertex n → Site 2)) := by
  intro e f hef
  induction e using Sym2.inductionOn with
  | _ x y =>
      induction f using Sym2.inductionOn with
      | _ u v =>
          simp only [Sym2.map_mk] at hef
          rw [Sym2.eq_iff] at hef ⊢
          rcases hef with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · exact Or.inl ⟨Subtype.ext hxu, Subtype.ext hyv⟩
          · exact Or.inr ⟨Subtype.ext hxv, Subtype.ext hyu⟩



theorem rlc_connectorAmbientMixedConfig_graphEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
    rlc_connectorRestrictConfig
        (rlc_connectorAmbientMixedConfig gamma gamma' tau) s(x, y) =
      tau s(x, y) := by
  have he : s((x : Site 2), (y : Site 2)) ∈
      rlc_connectorEdges gamma gamma' := hxy.2
  rw [rlc_connectorRestrictConfig, Sym2.map_mk,
    rlc_connectorAmbientMixedConfig_connectorEdge gamma gamma' tau he]
  congr 1
  apply rlc_sym2Map_subtypeVal_injective
  rw [rlc_connectorEdgeLift_map]
  rfl

theorem rlc_openSub_restrict_ambientMixed_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorRestrictConfig
          (rlc_connectorAmbientMixedConfig gamma gamma' tau)) =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau := by
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_connectorAmbientMixedConfig_graphEdge gamma gamma' tau hxy] at hopen
      exact hopen⟩
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_connectorAmbientMixedConfig_graphEdge gamma gamma' tau hxy]
      exact hopen⟩




noncomputable def rlc_connectorPIMSReflectedConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorRestrictConfig (rlc_dualReflectConfig
    (rlc_connectorAmbientMixedConfig gamma gamma' tau))

theorem rlc_connectorPIMSReflectedConfig_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau e =
      !(rlc_connectorAmbientMixedConfig gamma gamma' tau
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_connectorPIMSReflectedConfig rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
    (e.map Subtype.val)

theorem rlc_connectorPIMSReflectedConfig_of_preimage_connector {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma') :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau e =
      !(tau (rlc_connectorEdgeLift gamma gamma'
        (rlc_pimsEdgeEquiv (e.map Subtype.val)) he)) := by
  rw [rlc_connectorPIMSReflectedConfig_apply,
    rlc_connectorAmbientMixedConfig_connectorEdge gamma gamma' tau he]

theorem rlc_connectorPIMSReflectedConfig_of_preimage_trace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau e = false := by
  rw [rlc_connectorPIMSReflectedConfig_apply,
    rlc_connectorAmbientMixedConfig_traceEdge gamma gamma' tau he]
  rfl

theorem rlc_connectorPIMSReflectedConfig_of_preimage_exterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (hG : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau e = true := by
  rw [rlc_connectorPIMSReflectedConfig_apply]
  simp [rlc_connectorAmbientMixedConfig, hG, htrace]



noncomputable def rlc_connectorPIMSCollaredReflectedConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorRestrictConfig (rlc_dualReflectConfig
    (rlc_connectorAmbientCollaredConfig gamma gamma' tau))

theorem rlc_connectorPIMSCollaredReflectedConfig_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e =
      !(rlc_connectorAmbientCollaredConfig gamma gamma' tau
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_connectorPIMSCollaredReflectedConfig
    rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims
    (rlc_connectorAmbientCollaredConfig gamma gamma' tau)
    (e.map Subtype.val)

theorem rlc_connectorPIMSCollaredReflectedConfig_of_preimage_connector
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma') :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e =
      !(tau (rlc_connectorEdgeLift gamma gamma'
        (rlc_pimsEdgeEquiv (e.map Subtype.val)) he)) := by
  rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
    rlc_connectorAmbientCollaredConfig_connectorEdge gamma gamma' tau he]

theorem rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = false := by
  rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
    rlc_connectorAmbientCollaredConfig_traceEdge gamma gamma' tau he]
  rfl



theorem rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (htarget : e.map Subtype.val ∈ rlc_connectorEdges gamma gamma')
    (hG : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = false := by
  have hcollar := rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages
    gamma gamma' htarget hG htrace
  rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
    rlc_connectorAmbientCollaredConfig_collarEdge gamma gamma' tau hcollar]
  rfl




noncomputable def rlc_connectorPIMSCollaredParameter {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (e : Sym2 (RlcConnectorVertex n)) : Real :=
  if rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma' then p else 0

@[simp] theorem rlc_connectorPIMSCollaredParameter_of_preimage_connector
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma') :
    rlc_connectorPIMSCollaredParameter gamma gamma' p e = p := by
  simp [rlc_connectorPIMSCollaredParameter, he]

@[simp] theorem rlc_connectorPIMSCollaredParameter_of_preimage_exterior
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_connectorEdges gamma gamma') :
    rlc_connectorPIMSCollaredParameter gamma gamma' p e = 0 := by
  simp [rlc_connectorPIMSCollaredParameter, he]

@[simp] theorem rlc_connectorPIMSCollaredParameter_of_preimage_trace
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSCollaredParameter gamma gamma' p e = 0 := by
  apply rlc_connectorPIMSCollaredParameter_of_preimage_exterior
  rcases Finset.mem_union.mp he with hright | hleft
  · exact Finset.disjoint_left.mp
      (rlc_rightPathEdges_disjoint_connector gamma gamma') hright
  · exact Finset.disjoint_left.mp
      (rlc_leftPathEdges_disjoint_connector gamma gamma') hleft



noncomputable def rlc_connectorPIMSVariableGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorFiniteGraph gamma gamma').Adj x y ∧
    rlc_pimsEdgeEquiv (s(x, y).map Subtype.val) ∈
      rlc_connectorEdges gamma gamma'
  symm := by
    rintro x y ⟨hxy, hsource⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using hsource⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorPIMSVariableGraph_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorPIMSVariableGraph gamma gamma').Adj :=
  Classical.decRel _




noncomputable def rlc_connectorPIMSTraceGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorFiniteGraph gamma gamma').Adj x y ∧
    rlc_pimsEdgeEquiv (s(x, y).map Subtype.val) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  symm := by
    rintro x y ⟨hxy, hsource⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using hsource⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorPIMSTraceGraph_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorPIMSTraceGraph gamma gamma').Adj :=
  Classical.decRel _




noncomputable def rlc_connectorPIMSExteriorGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorFiniteGraph gamma gamma').Adj x y ∧
    rlc_pimsEdgeEquiv (s(x, y).map Subtype.val) ∉
      rlc_connectorEdges gamma gamma' ∧
    rlc_pimsEdgeEquiv (s(x, y).map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  symm := by
    rintro x y ⟨hxy, hsource, htrace⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using hsource,
      by simpa [Sym2.eq_swap] using htrace⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorPIMSExteriorGraph_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorPIMSExteriorGraph gamma gamma').Adj :=
  Classical.decRel _





def RlcConnectorPIMSExteriorTraceLocal {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∀ ⦃x y : RlcConnectorVertex n⦄,
    (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y →
      (rlc_connectorOnRight gamma x ∧ rlc_connectorOnRight gamma y) ∨
      (rlc_connectorOnLeft gamma' x ∧ rlc_connectorOnLeft gamma' y)





def RlcConnectorPIMSExtremalSelectionExteriorLocality (n : Int) : Prop :=
  ∀ pair : RlcDiagonalPathPair n,
    (rlc_extremalPairCandidate pair).Nonempty →
      RlcConnectorPIMSExteriorTraceLocal pair.1 pair.2



theorem rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorPIMSExteriorTraceLocal gamma gamma' ↔
      rlc_connectorPIMSExteriorGraph gamma gamma' ≤
        rlc_connectorSeparateWiring gamma gamma' := by
  constructor
  · intro hlocal x y hxy
    rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj]
    rcases hlocal hxy with hright | hleft
    · left
      rw [Lattice.boundaryCliqueGraph_adj]
      exact ⟨hxy.ne, hright⟩
    · right
      rw [Lattice.boundaryCliqueGraph_adj]
      exact ⟨hxy.ne, hleft⟩
  · intro hle x y hxy
    have hsep := hle hxy
    rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
    rcases hsep with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact Or.inl hright.2
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact Or.inr hleft.2



theorem rlc_connectorPIMSExteriorTraceLocal_or_badEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorPIMSExteriorTraceLocal gamma gamma' ∨
      ∃ x y : RlcConnectorVertex n,
        (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y ∧
        ¬ ((rlc_connectorOnRight gamma x ∧
              rlc_connectorOnRight gamma y) ∨
            (rlc_connectorOnLeft gamma' x ∧
              rlc_connectorOnLeft gamma' y)) := by
  classical
  by_cases hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma'
  · exact Or.inl hlocal
  · right
    unfold RlcConnectorPIMSExteriorTraceLocal at hlocal
    push Not at hlocal
    obtain ⟨x, y, hxy, hright, hleft⟩ := hlocal
    refine ⟨x, y, hxy, ?_⟩
    rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact hright hx hy
    · exact hleft hx hy




theorem not_rlc_connectorPIMSExtremalSelectionExteriorLocality_iff {n : Int} :
    ¬ RlcConnectorPIMSExtremalSelectionExteriorLocality n ↔
      ∃ (pair : RlcDiagonalPathPair n)
        (omega : ConfigSpace (Sym2 (Site 2)))
        (x y : RlcConnectorVertex n),
        omega ∈ rlc_extremalPairCandidate pair ∧
        (rlc_connectorPIMSExteriorGraph pair.1 pair.2).Adj x y ∧
        ¬ ((rlc_connectorOnRight pair.1 x ∧
              rlc_connectorOnRight pair.1 y) ∨
            (rlc_connectorOnLeft pair.2 x ∧
              rlc_connectorOnLeft pair.2 y)) := by
  classical
  constructor
  · intro hselection
    unfold RlcConnectorPIMSExtremalSelectionExteriorLocality at hselection
    push Not at hselection
    obtain ⟨pair, ⟨omega, hpair⟩, hlocal⟩ := hselection
    rcases rlc_connectorPIMSExteriorTraceLocal_or_badEdge pair.1 pair.2 with
      hgood | ⟨x, y, hxy, hbad⟩
    · exact (hlocal hgood).elim
    · exact ⟨pair, omega, x, y, hpair, hxy, hbad⟩
  · rintro ⟨pair, omega, x, y, hpair, hxy, hbad⟩ hselection
    exact hbad (hselection pair ⟨omega, hpair⟩ hxy)

private def rlc_extremalSelectionExteriorBadX : RlcConnectorVertex 1 :=
  ⟨![1, 0], by simp [mem_rect]⟩

private def rlc_extremalSelectionExteriorBadY : RlcConnectorVertex 1 :=
  ⟨![2, 0], by simp [mem_rect]⟩

private theorem rlc_extremalSelection_one_zero_mem_originRegion :
    (![1, 0] : Site 2) ∈ rlc_connectorOriginRegion
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  rw [rlc_connectorOriginRegion]
  simp only [Set.Finite.mem_toFinset]
  let z : Site 2 := ![1, 0]
  have hz : z ∈ rlc_connectorAllowed rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp [z, rlc_connectorBox, mem_rect]
    · rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp [z, rlc_flipX, rlc_flipXFun]
  have ho : origin 2 ∈ rlc_connectorAllowed
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp [rlc_connectorBox, mem_rect, origin]
    · rw [show origin 2 = (![0, 0] : Site 2) by
        ext i
        fin_cases i <;> rfl]
      rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp [rlc_flipX, rlc_flipXFun]
  refine ⟨hz, ho, ?_⟩
  exact (show ((hypercubicLattice 2).induce
      (rlc_connectorAllowed rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft : Set (Site 2))).Adj
      ⟨origin 2, ho⟩ ⟨z, hz⟩ by
        change (hypercubicLattice 2).Adj (origin 2) z
        simp [z, hypercubicLattice_adj, Fin.sum_univ_two, origin]).reachable

private theorem rlc_extremalSelection_bad_target_mem_connectorEdges :
    s((![1, 0] : Site 2), ![2, 0]) ∈ rlc_connectorEdges
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  rw [rlc_connectorEdges, Finset.mem_filter]
  constructor
  · rw [mem_edgesWithinFinset]
    exact ⟨![1, 0], by simp [rlc_connectorBox, mem_rect],
      ![2, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
  · exact ⟨![1, 0], rlc_extremalSelection_one_zero_mem_originRegion,
      Sym2.mem_mk_left _ _⟩

private theorem rlc_extremalSelection_bad_source_not_connectorEdges :
    s((![-2, -1] : Site 2), ![-2, 0]) ∉ rlc_connectorEdges
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  intro hsource
  rw [rlc_connectorEdges, Finset.mem_filter] at hsource
  obtain ⟨z, hzRegion, hzEdge⟩ := hsource.2
  have hzSet : z ∈ rlc_connectorOriginRegionSet
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
    simpa [rlc_connectorOriginRegion] using hzRegion
  obtain ⟨hzAllowed, _ho, _hreach⟩ := hzSet
  have hzNotBarrier := (Finset.mem_sdiff.mp hzAllowed).2
  rw [Sym2.mem_iff] at hzEdge
  rcases hzEdge with rfl | rfl
  · apply hzNotBarrier
    rw [rlc_connectorBarrier,
      rlc_traceSplitCounterexample_right_vertices,
      rlc_traceSplitCounterexample_left_vertices]
    simp [rlc_flipX, rlc_flipXFun]
  · apply hzNotBarrier
    rw [rlc_connectorBarrier,
      rlc_traceSplitCounterexample_right_vertices,
      rlc_traceSplitCounterexample_left_vertices]
    simp [rlc_flipX, rlc_flipXFun]

private theorem rlc_extremalSelection_bad_source_not_traceEdges :
    s((![-2, -1] : Site 2), ![-2, 0]) ∉
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
  intro hsource
  rcases Finset.mem_union.mp hsource with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleRight.1 hright
    rw [rlc_traceSplitCounterexample_right_vertices] at hends
    simp at hends
  · have hends := rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleLeft.1 hleft
    rw [rlc_traceSplitCounterexample_left_vertices] at hends
    simp at hends



theorem rlc_extremalSelection_exterior_badEdge :
    (rlc_connectorPIMSExteriorGraph
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj
        rlc_extremalSelectionExteriorBadX
        rlc_extremalSelectionExteriorBadY ∧
      ¬ ((rlc_connectorOnRight rlc_traceSplitCounterexampleRight
            rlc_extremalSelectionExteriorBadX ∧
          rlc_connectorOnRight rlc_traceSplitCounterexampleRight
            rlc_extremalSelectionExteriorBadY) ∨
        (rlc_connectorOnLeft rlc_traceSplitCounterexampleLeft
            rlc_extremalSelectionExteriorBadX ∧
          rlc_connectorOnLeft rlc_traceSplitCounterexampleLeft
            rlc_extremalSelectionExteriorBadY)) := by
  constructor
  · refine ⟨⟨?_, rlc_extremalSelection_bad_target_mem_connectorEdges⟩,
      ?_, ?_⟩
    · simp [rlc_extremalSelectionExteriorBadX,
        rlc_extremalSelectionExteriorBadY, hypercubicLattice_adj,
        Fin.sum_univ_two]
    · simpa [rlc_extremalSelectionExteriorBadX,
        rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
        rlc_pimsEdgeEquiv_horizontal] using
          rlc_extremalSelection_bad_source_not_connectorEdges
    · simpa [rlc_extremalSelectionExteriorBadX,
        rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
        rlc_pimsEdgeEquiv_horizontal] using
          rlc_extremalSelection_bad_source_not_traceEdges
  · rintro (⟨hx, _hy⟩ | ⟨hx, _hy⟩)
    · change (![1, 0] : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 at hx
      rw [rlc_traceSplitCounterexample_right_vertices] at hx
      simp at hx
    · change (![1, 0] : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 at hx
      rw [rlc_traceSplitCounterexample_left_vertices] at hx
      simp at hx




theorem not_rlc_connectorPIMSExtremalSelectionExteriorLocality :
    ¬ RlcConnectorPIMSExtremalSelectionExteriorLocality 1 := by
  rw [not_rlc_connectorPIMSExtremalSelectionExteriorLocality_iff]
  exact ⟨(rlc_traceSplitCounterexampleRight,
      rlc_traceSplitCounterexampleLeft),
    rlc_extremalSelectionCounterexampleConfig,
    rlc_extremalSelectionExteriorBadX,
    rlc_extremalSelectionExteriorBadY,
    rlc_extremalSelection_extremalPairCandidate,
    rlc_extremalSelection_exterior_badEdge.1,
    rlc_extremalSelection_exterior_badEdge.2⟩



theorem rlc_connectorPIMSExteriorGraph_le_separateWiring_of_extremalSelection
    {n : Int}
    (hselection : RlcConnectorPIMSExtremalSelectionExteriorLocality n)
    (pair : RlcDiagonalPathPair n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hpair : omega ∈ rlc_extremalPairCandidate pair) :
    rlc_connectorPIMSExteriorGraph pair.1 pair.2 ≤
      rlc_connectorSeparateWiring pair.1 pair.2 :=
  (rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring
    pair.1 pair.2).mp (hselection pair ⟨omega, hpair⟩)



noncomputable def rlc_connectorPIMSExteriorWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := x ≠ y ∧
    (rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y
  symm := by
    rintro x y ⟨hne, hxy⟩
    exact ⟨hne.symm, hxy.symm⟩
  loopless := ⟨fun x hxx => hxx.1 rfl⟩

noncomputable instance rlc_connectorPIMSExteriorWiring_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorPIMSExteriorWiring gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_connectorPIMSExterior_reachable_iff_wiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y ↔
      (rlc_connectorPIMSExteriorWiring gamma gamma').Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    exact ⟨huv.ne, huv.reachable⟩
  · apply rlc_reachable_of_step_reachable
    intro u v huv
    exact huv.2



theorem rlc_connectorPIMSExterior_sup_reachable_iff_wiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (x y : RlcConnectorVertex n) :
    (H ⊔ rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y ↔
      (H ⊔ rlc_connectorPIMSExteriorWiring gamma gamma').Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    rcases huv with hH | hext
    · exact Or.inl hH
    · exact Or.inr ⟨hext.ne, hext.reachable⟩
  · apply rlc_reachable_of_step_reachable
    intro u v huv
    rcases huv with hH | hwire
    · exact (show (H ⊔
          rlc_connectorPIMSExteriorGraph gamma gamma').Adj u v
        from Or.inl hH).reachable
    · exact hwire.2.mono le_sup_right




theorem rlc_connectorFiniteGraph_eq_PIMS_preimage_partition {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorFiniteGraph gamma gamma' =
      (rlc_connectorPIMSVariableGraph gamma gamma' ⊔
        rlc_connectorPIMSTraceGraph gamma gamma') ⊔
      rlc_connectorPIMSExteriorGraph gamma gamma' := by
  ext x y
  let source := rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)
  constructor
  · intro hxy
    by_cases hsource : source ∈ rlc_connectorEdges gamma gamma'
    · exact Or.inl (Or.inl ⟨hxy, hsource⟩)
    · by_cases htrace :
          source ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · exact Or.inl (Or.inr ⟨hxy, htrace⟩)
      · exact Or.inr ⟨hxy, hsource, htrace⟩
  · rintro ((⟨hxy, _⟩ | ⟨hxy, _⟩) | ⟨hxy, _, _⟩) <;> exact hxy


theorem rlc_openSub_PIMS_trace_eq_bot {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorPIMSTraceGraph gamma gamma')
      (rlc_connectorPIMSReflectedConfig gamma gamma' tau) = ⊥ := by
  ext x y
  rw [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    have hclosed := rlc_connectorPIMSReflectedConfig_of_preimage_trace
      gamma gamma' tau s(x, y) hxy.2
    exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · intro hbot
    exact hbot.elim




theorem rlc_openSub_PIMS_eq_variable_sup_exterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSReflectedConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma')
          (rlc_connectorPIMSReflectedConfig gamma gamma' tau) ⊔
        rlc_connectorPIMSExteriorGraph gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj, FK.openSub_adj]
  let source := rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)
  constructor
  · rintro ⟨hxy, hopen⟩
    by_cases hsource : source ∈ rlc_connectorEdges gamma gamma'
    · exact Or.inl ⟨⟨hxy, hsource⟩, hopen⟩
    · by_cases htrace :
          source ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · have hclosed := rlc_connectorPIMSReflectedConfig_of_preimage_trace
          gamma gamma' tau s(x, y) htrace
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
      · exact Or.inr ⟨hxy, hsource, htrace⟩
  · rintro (⟨⟨hxy, hsource⟩, hopen⟩ | ⟨hxy, hsource, htrace⟩)
    · exact ⟨hxy, hopen⟩
    · refine ⟨hxy, ?_⟩
      exact rlc_connectorPIMSReflectedConfig_of_preimage_exterior
        gamma gamma' tau s(x, y) hsource htrace




theorem rlc_openSub_PIMSCollared_eq_variable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma')
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau) := by
  ext x y
  rw [FK.openSub_adj, FK.openSub_adj]
  let source := rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)
  constructor
  · rintro ⟨hxy, hopen⟩
    by_cases hsource : source ∈ rlc_connectorEdges gamma gamma'
    · exact ⟨⟨hxy, hsource⟩, hopen⟩
    · by_cases htrace :
          source ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · have hclosed :=
          rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace
            gamma gamma' tau s(x, y) htrace
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
      · have hclosed :=
          rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
            gamma gamma' tau s(x, y) hxy.2 hsource htrace
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · rintro ⟨⟨hxy, _hsource⟩, hopen⟩
    exact ⟨hxy, hopen⟩



noncomputable def rlc_connectorComponentWiring {n : Int}
    (H : SimpleGraph (RlcConnectorVertex n)) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := x ≠ y ∧ H.Reachable x y
  symm := by
    rintro x y ⟨hne, hxy⟩
    exact ⟨hne.symm, hxy.symm⟩
  loopless := ⟨fun x hxx => hxx.1 rfl⟩

noncomputable instance rlc_connectorComponentWiring_decidableAdj {n : Int}
    (H : SimpleGraph (RlcConnectorVertex n)) :
    DecidableRel (rlc_connectorComponentWiring H).Adj :=
  Classical.decRel _



def RlcConnectorExteriorOneAttachment {n : Int}
    (H : SimpleGraph (RlcConnectorVertex n)) : Prop :=
  ∀ {x y : RlcConnectorVertex n}, H.Reachable x y → x = y


theorem rlc_connectorComponentWiring_eq_bot_of_oneAttachment {n : Int}
    (H : SimpleGraph (RlcConnectorVertex n))
    (hattach : RlcConnectorExteriorOneAttachment H) :
    rlc_connectorComponentWiring H = ⊥ := by
  ext x y
  constructor
  · intro hxy
    exact (hxy.1 (hattach hxy.2)).elim
  · intro hbot
    exact hbot.elim



noncomputable def rlc_connectorPIMSCollaredExteriorOpenGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (RlcConnectorVertex n) :=
  FK.openSub
    (rlc_connectorPIMSTraceGraph gamma gamma' ⊔
      rlc_connectorPIMSExteriorGraph gamma gamma')
    (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau)


theorem rlc_connectorPIMSCollaredExteriorOpenGraph_eq_bot {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau = ⊥ := by
  ext x y
  rw [rlc_connectorPIMSCollaredExteriorOpenGraph, FK.openSub_adj]
  constructor
  · rintro ⟨hclass, hopen⟩
    rcases hclass with htrace | hext
    · have hclosed :=
        rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace
          gamma gamma' tau s(x, y) htrace.2
      exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
    · have hclosed :=
        rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
          gamma gamma' tau s(x, y) hext.1.2 hext.2.1 hext.2.2
      exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · intro hbot
    exact hbot.elim



theorem rlc_connectorPIMSCollaredExterior_oneAttachment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    RlcConnectorExteriorOneAttachment
      (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) := by
  intro x y hxy
  rw [rlc_connectorPIMSCollaredExteriorOpenGraph_eq_bot] at hxy
  exact SimpleGraph.reachable_bot.mp hxy



theorem rlc_connectorPIMSCollaredInducedWiring_eq_bot {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorComponentWiring
        (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) = ⊥ :=
  rlc_connectorComponentWiring_eq_bot_of_oneAttachment _
      (rlc_connectorPIMSCollaredExterior_oneAttachment gamma gamma' tau)




noncomputable def rlc_connectorPIMSAssembleConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  fun e => if e ∈ (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet
    then rho e
    else decide (e ∈ (rlc_connectorPIMSExteriorGraph gamma gamma').edgeSet)



noncomputable def rlc_connectorPIMSVariableConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  fun e => if e ∈ (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet
    then rho e else false

theorem rlc_openSub_PIMSVariableConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSVariableConfig gamma gamma' rho) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho := by
  ext x y
  rw [FK.openSub_adj, FK.openSub_adj]
  by_cases hvar : (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y
  · simp [rlc_connectorPIMSVariableConfig, SimpleGraph.mem_edgeSet,
      hvar, hvar.1]
  · simp [rlc_connectorPIMSVariableConfig, SimpleGraph.mem_edgeSet, hvar]


theorem rlc_openSub_PIMSAssembleConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSAssembleConfig gamma gamma' rho) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho ⊔
        rlc_connectorPIMSExteriorGraph gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj, FK.openSub_adj]
  by_cases hvar : (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y
  · have hnotext :
        ¬ (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y :=
      fun hext => hext.2.1 hvar.2
    simp [rlc_connectorPIMSAssembleConfig, SimpleGraph.mem_edgeSet,
      hvar, hnotext, hvar.1]
  · by_cases hext :
        (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y
    · simp [rlc_connectorPIMSAssembleConfig, SimpleGraph.mem_edgeSet,
        hvar, hext, hext.1]
    · simp [rlc_connectorPIMSAssembleConfig, SimpleGraph.mem_edgeSet,
        hvar, hext]




theorem rlc_connectorPIMSReflectedConfig_open_of_masked_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (hnotTrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hopen : rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau))
      (e.map Subtype.val) = true) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau e = true := by
  rw [rlc_dualReflectConfig_eq_pims] at hopen
  rw [rlc_connectorPIMSReflectedConfig_apply]
  let source := rlc_pimsEdgeEquiv (e.map Subtype.val)
  by_cases hG : source ∈ rlc_connectorEdges gamma gamma'
  · simpa [source, rlc_maskConfig, hG] using hopen
  · have hsource :
        rlc_connectorAmbientMixedConfig gamma gamma' tau source = false := by
      simp [rlc_connectorAmbientMixedConfig, hG, hnotTrace, source]
    rw [hsource]
    rfl




noncomputable def rlc_connectorReflectedDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    Sym2 (Site 2) :=
  s(rlc_dualReflect (Ising.kwg_flankLeft
      (rlc_connectorAugmentedPlanarDomain gamma gamma') f),
    rlc_dualReflect (Ising.kwg_flankRight
      (rlc_connectorAugmentedPlanarDomain gamma gamma') f))



@[simp] theorem rlc_pimsEdgeEquiv_connectorReflectedDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_pimsEdgeEquiv
        (rlc_connectorReflectedDualEdge gamma gamma' f) =
      Ising.kwg_embeddedEdge
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f := by
  rw [rlc_connectorReflectedDualEdge,
    rlc_pimsEdgeEquiv_reflected_mk_of_adj
      (Ising.kwg_flanks_adj _ f), Ising.kwg_flanks_shared]




theorem rlc_connectorReflectedDualEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_connectorReflectedDualEdge gamma gamma') := by
  intro e f hef
  have hemb := congrArg rlc_pimsEdgeEquiv hef
  simp only [rlc_pimsEdgeEquiv_connectorReflectedDualEdge] at hemb
  apply Subtype.ext
  apply rlc_sym2Map_subtypeVal_injective
  simpa [Ising.kwg_embeddedEdge,
    rlc_connectorAugmentedPlanarDomain] using hemb












abbrev RlcConnectorOuterDualVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  RlcConnectorVertex n ⊕
    ((Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma') × Bool) ⊕
      Ising.kwg_Face
        (rlc_connectorAugmentedPlanarDomain gamma gamma'))

noncomputable instance rlc_connectorOuterDualVertexFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcConnectorOuterDualVertex gamma gamma') := by
  letI : Fintype (Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :=
    Fintype.ofFinite _
  infer_instance

noncomputable instance rlc_connectorOuterDualVertexDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcConnectorOuterDualVertex gamma gamma') :=
  Classical.decEq _


def rlc_connectorOuterTargetVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorVertex n → RlcConnectorOuterDualVertex gamma gamma' :=
  Sum.inl



def rlc_connectorOuterPort {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) (side : Bool) :
    RlcConnectorOuterDualVertex gamma gamma' :=
  Sum.inr (Sum.inl (f, side))


def rlc_connectorOuterFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    RlcConnectorOuterDualVertex gamma gamma' :=
  Sum.inr (Sum.inr C)



def RlcConnectorRetainedDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) : Prop :=
  ∃ e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet,
    e.1.map Subtype.val =
      rlc_connectorReflectedDualEdge gamma gamma' f

noncomputable instance rlc_connectorRetainedDualEdgeDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    Decidable (RlcConnectorRetainedDualEdge gamma gamma' f) :=
  Classical.dec _



noncomputable def rlc_connectorOuterDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    Sym2 (RlcConnectorOuterDualVertex gamma gamma') :=
  if h : RlcConnectorRetainedDualEdge gamma gamma' f then
    h.choose.1.map (rlc_connectorOuterTargetVertex gamma gamma')
  else
    s(rlc_connectorOuterPort gamma gamma' f false,
      rlc_connectorOuterPort gamma gamma' f true)

theorem rlc_connectorOuterTargetVertex_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorOuterTargetVertex gamma gamma') :=
  Sum.inl_injective



theorem rlc_connectorOuterDualEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_connectorOuterDualEdge gamma gamma') := by
  intro f g hfg
  unfold rlc_connectorOuterDualEdge at hfg
  split at hfg <;> split at hfg
  · rename_i hf hg
    have hedge : hf.choose.1 = hg.choose.1 := by
      apply Sym2.map.injective
        (rlc_connectorOuterTargetVertex_injective gamma gamma')
      exact hfg
    apply rlc_connectorReflectedDualEdge_injective gamma gamma'
    rw [← hf.choose_spec, ← hg.choose_spec, hedge]
  · rename_i hf hg
    revert hfg
    induction hf.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_connectorOuterTargetVertex,
          rlc_connectorOuterPort] at hfg
  · rename_i hf hg
    revert hfg
    induction hg.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_connectorOuterTargetVertex,
          rlc_connectorOuterPort] at hfg
  · rename_i hf hg
    simpa [rlc_connectorOuterPort, Sym2.eq_iff] using hfg


noncomputable def rlc_connectorOuterFaceProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorOuterDualVertex gamma gamma' →
      Ising.kwg_Face (rlc_connectorAugmentedPlanarDomain gamma gamma')
  | Sum.inl x => BeffaraDC.pfdFace
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)
  | Sum.inr (Sum.inl (f, false)) => BeffaraDC.pfdFace
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (Ising.kwg_flankLeft
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inl (f, true)) => BeffaraDC.pfdFace
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (Ising.kwg_flankRight
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inr C) => C


def RlcConnectorOuterIsFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorOuterDualVertex gamma gamma' → Prop
  | Sum.inr (Sum.inr _) => True
  | _ => False

noncomputable instance rlc_connectorOuterIsFaceDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (RlcConnectorOuterIsFace gamma gamma') :=
  Classical.decPred _



noncomputable def rlc_connectorOuterSpokeGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorOuterDualVertex gamma gamma') where
  Adj x y := x ≠ y ∧
    rlc_connectorOuterFaceProjection gamma gamma' x =
      rlc_connectorOuterFaceProjection gamma gamma' y ∧
    (RlcConnectorOuterIsFace gamma gamma' x ∨
      RlcConnectorOuterIsFace gamma gamma' y)
  symm := by
    rintro x y ⟨hne, hface, hghost⟩
    exact ⟨hne.symm, hface.symm, hghost.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance rlc_connectorOuterSpokeGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorOuterSpokeGraph gamma gamma').Adj :=
  Classical.decRel _

@[simp] theorem rlc_connectorOuterFaceProjection_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterFaceProjection gamma gamma'
        (rlc_connectorOuterFace gamma gamma' C) = C :=
  rfl



theorem rlc_connectorOuterSpoke_adj_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorOuterDualVertex gamma gamma')
    (hx : ¬RlcConnectorOuterIsFace gamma gamma' x) :
    (rlc_connectorOuterSpokeGraph gamma gamma').Adj x
      (rlc_connectorOuterFace gamma gamma'
        (rlc_connectorOuterFaceProjection gamma gamma' x)) := by
  refine ⟨?_, rfl, Or.inr trivial⟩
  intro h
  rw [h] at hx
  exact hx trivial



noncomputable def rlc_connectorOuterRandomGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorOuterDualVertex gamma gamma') where
  Adj x y := x ≠ y ∧ ∃ f, rlc_connectorOuterDualEdge gamma gamma' f = s(x, y)
  symm := by
    rintro x y ⟨hne, f, hf⟩
    exact ⟨hne.symm, f, hf.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance rlc_connectorOuterRandomGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorOuterRandomGraph gamma gamma').Adj :=
  Classical.decRel _



noncomputable def rlc_connectorOuterDualGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorOuterDualVertex gamma gamma') :=
  rlc_connectorOuterRandomGraph gamma gamma' ⊔
    rlc_connectorOuterSpokeGraph gamma gamma'

noncomputable instance rlc_connectorOuterDualGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorOuterDualGraph gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_connectorOuterDualEdge_ne_diag {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma'))
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    rlc_connectorOuterDualEdge gamma gamma' f ≠ s(x, x) := by
  unfold rlc_connectorOuterDualEdge
  split
  · rename_i hf
    have hedge := hf.choose.2
    revert hedge
    induction hf.choose.1 using Sym2.inductionOn with
    | _ u v =>
        intro hedge heq
        rw [SimpleGraph.mem_edgeSet] at hedge
        rw [Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with h | h
        · apply hedge.ne
          exact rlc_connectorOuterTargetVertex_injective gamma gamma'
            (h.1.trans h.2.symm)
        · apply hedge.ne
          exact rlc_connectorOuterTargetVertex_injective gamma gamma'
            (h.2.trans h.1.symm).symm
  · intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · have hbool : false = true := congrArg
        (fun z => match z with
          | Sum.inr (Sum.inl (_, side)) => side
          | _ => false) (h.1.trans h.2.symm)
      simp at hbool
    · have hbool : false = true := congrArg
        (fun z => match z with
          | Sum.inr (Sum.inl (_, side)) => side
          | _ => false) (h.1.trans h.2.symm)
      simp at hbool


theorem rlc_connectorOuterDualEdge_mem_random {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∈
      (rlc_connectorOuterRandomGraph gamma gamma').edgeSet := by
  induction hxy : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      refine ⟨?_, f, hxy⟩
      intro h
      subst y
      exact rlc_connectorOuterDualEdge_ne_diag gamma gamma' f x hxy



theorem rlc_connectorOuterRandom_edgeFinset {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset =
      Finset.univ.image (rlc_connectorOuterDualEdge gamma gamma') := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_image]
  constructor
  · intro he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeSet] at he
        exact ⟨he.2.choose, Finset.mem_univ _, he.2.choose_spec⟩
  · rintro ⟨f, _, rfl⟩
    exact rlc_connectorOuterDualEdge_mem_random gamma gamma' f



theorem rlc_pimsEdgeEquiv_mem_latticeEdge {e : Sym2 (Site 2)}
    (he : e ∈ (hypercubicLattice 2).edgeSet) :
    rlc_pimsEdgeEquiv e ∈ (hypercubicLattice 2).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      have hinv : (hypercubicLattice 2).Adj
          (rlc_dualReflect.symm x) (rlc_dualReflect.symm y) := by
        rw [rlc_adj_dualReflect]
        simpa using he
      rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
      obtain ⟨u, v, huv, hadj⟩ := sharedPrimalEdge_isLatticeEdge hinv
      rw [fci_faceEdgeEquiv_mk_of_adj hinv, huv]
      exact (SimpleGraph.mem_edgeSet _).mpr hadj






noncomputable def rlc_connectorReflectedTraceEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  rlc_reflectedPathEdges gamma.1 ∪ rlc_reflectedPathEdges gamma'.1


noncomputable def rlc_connectorFourTraceEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
    rlc_connectorReflectedTraceEdges gamma gamma'



noncomputable def rlc_connectorReflectedTraceWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (hypercubicLattice 2).Adj x.1 y.1 ∧
    s(x.1, y.1) ∈ rlc_connectorReflectedTraceEdges gamma gamma'
  symm := by
    rintro x y ⟨hxy, hedge⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using hedge⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorReflectedTraceWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorReflectedTraceWiring gamma gamma').Adj :=
  Classical.decRel _



def rlc_connectorFourTracePlanarDomain {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorVertex n
  finV := inferInstance
  decV := inferInstance
  G := rlc_connectorFiniteGraph gamma gamma' ⊔
    rlc_connectorTraceWiring gamma gamma' ⊔
      rlc_connectorReflectedTraceWiring gamma gamma'
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    rcases hxy with (hxy | hxy) | hxy
    · exact hxy.1
    · exact hxy.1
    · exact hxy.1




noncomputable def rlc_connectorForceFourTraceConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  fun e => if e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset then true
    else if e ∈
      (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset then false
    else tau e

@[simp] theorem rlc_connectorForceFourTraceConfig_exposed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (RlcConnectorVertex n)}
    (he : e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset) :
    rlc_connectorForceFourTraceConfig gamma gamma' tau e = true := by
  simp [rlc_connectorForceFourTraceConfig, he]

@[simp] theorem rlc_connectorForceFourTraceConfig_reflected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (RlcConnectorVertex n)}
    (he : e ∈
      (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset)
    (hnot : e ∉ (rlc_connectorTraceWiring gamma gamma').edgeFinset) :
    rlc_connectorForceFourTraceConfig gamma gamma' tau e = false := by
  simp [rlc_connectorForceFourTraceConfig, he, hnot]

@[simp] theorem rlc_connectorForceFourTraceConfig_corridor {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
    rlc_connectorForceFourTraceConfig gamma gamma' tau s(x, y) =
      tau s(x, y) := by
  have hnotExposed : s(x, y) ∉
      (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
    intro hmem
    exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma' hxy
      ((SimpleGraph.mem_edgeSet _).mp (SimpleGraph.mem_edgeFinset.mp hmem))
  have hnotReflected : s(x, y) ∉
      (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset := by
    intro hmem
    have href := (SimpleGraph.mem_edgeSet _).mp
      (SimpleGraph.mem_edgeFinset.mp hmem)
    rcases Finset.mem_union.mp href.2 with hright | hleft
    · unfold rlc_reflectedPathEdges at hright
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hright
      have hmapped : e.map rlc_flipX ∈
          rlc_connectorEdges gamma gamma' := by
        simpa [heq] using hxy.2
      have heConnector :=
        (rlc_connectorEdges_mem_map_flipX_iff gamma gamma' e).mpr hmapped
      exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma')) he heConnector
    · unfold rlc_reflectedPathEdges at hleft
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hleft
      have hmapped : e.map rlc_flipX ∈
          rlc_connectorEdges gamma gamma' := by
        simpa [heq] using hxy.2
      have heConnector :=
        (rlc_connectorEdges_mem_map_flipX_iff gamma gamma' e).mpr hmapped
      exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma')) he heConnector
  simp [rlc_connectorForceFourTraceConfig, hnotExposed, hnotReflected]



theorem rlc_openSub_fourTrace_force {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFourTracePlanarDomain gamma gamma').G
        (rlc_connectorForceFourTraceConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨(hfinite | htrace) | hreflected, hopen⟩
    · left
      refine ⟨hfinite, ?_⟩
      exact (rlc_connectorForceFourTraceConfig_corridor
        gamma gamma' tau hfinite).symm.trans hopen
    · exact Or.inr htrace
    · by_cases htrace :
          (rlc_connectorTraceWiring gamma gamma').Adj x y
      · exact Or.inr htrace
      · have hreflectedMem : s(x, y) ∈
            (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr hreflected)
        have htraceMem : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
          intro hmem
          exact htrace ((SimpleGraph.mem_edgeSet _).mp
            (SimpleGraph.mem_edgeFinset.mp hmem))
        have hclosed := rlc_connectorForceFourTraceConfig_reflected
          gamma gamma' tau hreflectedMem htraceMem
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · rintro (⟨hfinite, hopen⟩ | htrace)
    · refine ⟨Or.inl (Or.inl hfinite), ?_⟩
      exact (rlc_connectorForceFourTraceConfig_corridor
        gamma gamma' tau hfinite).trans hopen
    · refine ⟨Or.inl (Or.inr htrace), ?_⟩
      apply rlc_connectorForceFourTraceConfig_exposed gamma gamma' tau
      exact SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_edgeSet _).mpr htrace)





noncomputable def rlc_connectorCollaredWallEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  (rlc_connectorEdges gamma gamma' ∪
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)) ∪
    rlc_connectorPIMSExteriorPreimages gamma gamma'



noncomputable def rlc_connectorCollaredSites {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Site 2) :=
  rlc_connectorBox n ∪
    (rlc_connectorCollaredWallEdges gamma gamma').biUnion Sym2.toFinset


abbrev RlcConnectorCollaredVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {x : Site 2 // x ∈ rlc_connectorCollaredSites gamma gamma'}

noncomputable instance rlc_connectorCollaredVertexFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcConnectorCollaredVertex gamma gamma') :=
  Fintype.ofFinite _

noncomputable instance rlc_connectorCollaredVertexDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcConnectorCollaredVertex gamma gamma') :=
  Classical.decEq _


noncomputable def rlc_connectorCollaredWallGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorCollaredVertex gamma gamma') where
  Adj x y := (hypercubicLattice 2).Adj x.1 y.1 ∧
    s(x.1, y.1) ∈ rlc_connectorCollaredWallEdges gamma gamma'
  symm := by
    rintro x y ⟨hxy, hwall⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using hwall⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorCollaredWallGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorCollaredWallGraph gamma gamma').Adj :=
  Classical.decRel _


def rlc_connectorCollaredPlanarDomain {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorCollaredVertex gamma gamma'
  finV := inferInstance
  decV := inferInstance
  G := rlc_connectorCollaredWallGraph gamma gamma'
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    exact hxy.1

theorem rlc_connectorCollaredWallEdges_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_pimsEdgeEquiv e ∈
      rlc_connectorCollaredWallEdges gamma gamma' := by
  rw [rlc_connectorCollaredWallEdges]
  exact Finset.mem_union_right _
    (rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages
      gamma gamma' htarget hsource htrace)


theorem rlc_connectorCollaredWall_endpoint_mem {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
    {x : Site 2} (hx : x ∈ e) :
    x ∈ rlc_connectorCollaredSites gamma gamma' := by
  rw [rlc_connectorCollaredSites, Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  exact ⟨e, he, Sym2.mem_toFinset.mpr hx⟩



theorem rlc_connectorCollaredWallGraph_has_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (htargetLat : e ∈ (hypercubicLattice 2).edgeSet)
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    ∃ x y : RlcConnectorCollaredVertex gamma gamma',
      s(x.1, y.1) = rlc_pimsEdgeEquiv e ∧
        (rlc_connectorCollaredWallGraph gamma gamma').Adj x y := by
  have hwall := rlc_connectorCollaredWallEdges_preimage
    gamma gamma' htarget hsource htrace
  have hlat := rlc_pimsEdgeEquiv_mem_latticeEdge
    htargetLat
  induction hedge : rlc_pimsEdgeEquiv e using Sym2.inductionOn with
  | _ u v =>
    have hu : u ∈ rlc_pimsEdgeEquiv e := by rw [hedge]; simp
    have hv : v ∈ rlc_pimsEdgeEquiv e := by rw [hedge]; simp
    let x : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨u, rlc_connectorCollaredWall_endpoint_mem gamma gamma' hwall hu⟩
    let y : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨v, rlc_connectorCollaredWall_endpoint_mem gamma gamma' hwall hv⟩
    refine ⟨x, y, ?_, ?_⟩
    · simp [x, y]
    · refine ⟨?_, ?_⟩
      · rw [← SimpleGraph.mem_edgeSet, ← hedge]
        exact hlat
      · simpa [x, y, hedge] using hwall



theorem rlc_extremalSelection_bad_preimage_is_collaredWall :
    ∃ x y : RlcConnectorCollaredVertex
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft,
      s(x.1, y.1) = rlc_pimsEdgeEquiv
          s(rlc_extremalSelectionExteriorBadX.1,
            rlc_extremalSelectionExteriorBadY.1) ∧
        (rlc_connectorCollaredWallGraph
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft).Adj x y := by
  apply rlc_connectorCollaredWallGraph_has_preimage
  · exact rlc_extremalSelection_bad_target_mem_connectorEdges
  · simp [rlc_extremalSelectionExteriorBadX,
      rlc_extremalSelectionExteriorBadY, hypercubicLattice_adj,
      Fin.sum_univ_two]
  · simpa [rlc_extremalSelectionExteriorBadX,
      rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
      rlc_pimsEdgeEquiv_horizontal] using
        rlc_extremalSelection_bad_source_not_connectorEdges
  · simpa [rlc_extremalSelectionExteriorBadX,
      rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
      rlc_pimsEdgeEquiv_horizontal] using
        rlc_extremalSelection_bad_source_not_traceEdges

def rlc_extremalSelectionBadCollarX : RlcConnectorVertex 1 :=
  ⟨![-2, -1], by simp [mem_rect]⟩

def rlc_extremalSelectionBadCollarY : RlcConnectorVertex 1 :=
  ⟨![-2, 0], by simp [mem_rect]⟩



def rlc_connectorVertexToCollared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorVertex n → RlcConnectorCollaredVertex gamma gamma' :=
  fun x => ⟨x.1, Finset.mem_union_left _ (by
    change x.1 ∈ (rect_finite (-2 * n) (2 * n) (-n) n).toFinset
    exact (Set.Finite.mem_toFinset
      (rect_finite (-2 * n) (2 * n) (-n) n)).mpr x.2)⟩

theorem rlc_connectorVertexToCollared_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_connectorVertexToCollared gamma gamma') := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : RlcConnectorCollaredVertex gamma gamma' => z.1) hxy



theorem rlc_extremalSelection_badCollar_inside_not_augmented :
    (rlc_connectorCollaredWallGraph
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj
        (rlc_connectorVertexToCollared
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_extremalSelectionBadCollarX)
        (rlc_connectorVertexToCollared
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_extremalSelectionBadCollarY) ∧
      ¬(rlc_connectorAugmentedPlanarDomain
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft).G.Adj
          rlc_extremalSelectionBadCollarX
          rlc_extremalSelectionBadCollarY := by
  have hwall : s((![-2, -1] : Site 2), ![-2, 0]) ∈
      rlc_connectorCollaredWallEdges
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorCollaredWallEdges]
    apply Finset.mem_union_right
    apply rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_extremalSelection_bad_target_mem_connectorEdges
    · exact rlc_extremalSelection_bad_source_not_connectorEdges
    · exact rlc_extremalSelection_bad_source_not_traceEdges
  constructor
  · refine ⟨?_, ?_⟩
    · simp [rlc_connectorVertexToCollared,
        rlc_extremalSelectionBadCollarX,
        rlc_extremalSelectionBadCollarY,
        hypercubicLattice_adj, Fin.sum_univ_two]
    · simpa [rlc_connectorVertexToCollared,
        rlc_extremalSelectionBadCollarX,
        rlc_extremalSelectionBadCollarY] using hwall
  · rintro (hfinite | htrace)
    · exact rlc_extremalSelection_bad_source_not_connectorEdges
        (by simpa [rlc_extremalSelectionBadCollarX,
          rlc_extremalSelectionBadCollarY] using hfinite.2)
    · exact rlc_extremalSelection_bad_source_not_traceEdges
        (by simpa [rlc_extremalSelectionBadCollarX,
          rlc_extremalSelectionBadCollarY] using htrace.2)



theorem rlc_connectorAugmented_adj_collared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y) :
    (rlc_connectorCollaredPlanarDomain gamma gamma').G.Adj
      (rlc_connectorVertexToCollared gamma gamma' x)
      (rlc_connectorVertexToCollared gamma gamma' y) := by
  refine ⟨(rlc_connectorAugmentedPlanarDomain gamma gamma').isSub hxy, ?_⟩
  rw [rlc_connectorCollaredWallEdges]
  apply Finset.mem_union_left
  rw [Finset.mem_union]
  rcases hxy with hfinite | htrace
  · exact Or.inl hfinite.2
  · exact Or.inr htrace.2



def rlc_connectorAugmentedEdgeToCollared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma') →
      Ising.kwg_Edge (rlc_connectorCollaredPlanarDomain gamma gamma') :=
  fun e => ⟨e.1.map (rlc_connectorVertexToCollared gamma gamma'), by
    have he := e.2
    induction hedge : e.1 using Sym2.inductionOn with
    | _ x y =>
      rw [hedge, SimpleGraph.mem_edgeSet] at he
      change (rlc_connectorCollaredWallGraph gamma gamma').Adj
        (rlc_connectorVertexToCollared gamma gamma' x)
        (rlc_connectorVertexToCollared gamma gamma' y)
      exact rlc_connectorAugmented_adj_collared gamma gamma' he⟩

theorem rlc_connectorAugmentedEdgeToCollared_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorAugmentedEdgeToCollared gamma gamma') := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective
    (rlc_connectorVertexToCollared_injective gamma gamma')
    (congrArg Subtype.val hef)



theorem rlc_connectorCollaredWall_mem_imageGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    e ∈ (Lattice.imageGraph
      (rlc_connectorCollaredPlanarDomain gamma gamma')).edgeSet := by
  induction hedge : e using Sym2.inductionOn with
  | _ u v =>
    have hu : u ∈ e := by rw [hedge]; simp
    have hv : v ∈ e := by rw [hedge]; simp
    let x : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨u, rlc_connectorCollaredWall_endpoint_mem gamma gamma' he hu⟩
    let y : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨v, rlc_connectorCollaredWall_endpoint_mem gamma gamma' he hv⟩
    rw [SimpleGraph.mem_edgeSet, Lattice.imageGraph_adj]
    refine ⟨x, y, ⟨?_, ?_⟩, rfl, rfl⟩
    · exact (SimpleGraph.mem_edgeSet _).mp (hedge ▸ hlat)
    · simpa [x, y] using (hedge ▸ he)


theorem rlc_connectorCollaredWall_blocks_faceStep {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet)
    {f g : Site 2}
    (hshared : sharedPrimalEdge f g = e) :
    ¬ (whb_faceRegion (Lattice.imageGraph
      (rlc_connectorCollaredPlanarDomain gamma gamma'))).Adj f g := by
  intro hface
  have hnot := (whb_faceRegion_adj _ f g).mp hface |>.2
  apply hnot
  rw [hshared]
  exact rlc_connectorCollaredWall_mem_imageGraph
    gamma gamma' he hlat



theorem rlc_connectorCollared_preimage_blocks_faceStep {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (htargetLat : e ∈ (hypercubicLattice 2).edgeSet)
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    {f g : Site 2}
    (hshared : sharedPrimalEdge f g = rlc_pimsEdgeEquiv e) :
    ¬ (whb_faceRegion (Lattice.imageGraph
      (rlc_connectorCollaredPlanarDomain gamma gamma'))).Adj f g := by
  apply rlc_connectorCollaredWall_blocks_faceStep gamma gamma'
    (rlc_connectorCollaredWallEdges_preimage
      gamma gamma' htarget hsource htrace)
    (rlc_pimsEdgeEquiv_mem_latticeEdge htargetLat) hshared



theorem rlc_connectorEdgeLift_mem_finiteGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : Sym2 (Site 2)) (he : e ∈ rlc_connectorEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    rlc_connectorEdgeLift gamma gamma' e he ∈
      (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
  have hmap := rlc_connectorEdgeLift_map gamma gamma' e he
  revert hmap
  induction rlc_connectorEdgeLift gamma gamma' e he using
      Sym2.inductionOn with
  | _ x y =>
      intro hmap
      rw [Sym2.map_mk] at hmap
      rw [SimpleGraph.mem_edgeSet]
      refine ⟨?_, ?_⟩
      · apply (SimpleGraph.mem_edgeSet _).mp
        rw [hmap]
        exact hlat
      · rw [hmap]
        exact he





theorem rlc_connectorOuterRandomGraph_adj_target {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_connectorOuterRandomGraph gamma gamma').Adj
        (rlc_connectorOuterTargetVertex gamma gamma' x)
        (rlc_connectorOuterTargetVertex gamma gamma' y) ↔
      (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y := by
  constructor
  · rintro ⟨_, f, hf⟩
    unfold rlc_connectorOuterDualEdge at hf
    split at hf
    · rename_i hret
      have hedge : hret.choose.1 = s(x, y) := by
        apply Sym2.map.injective
          (rlc_connectorOuterTargetVertex_injective gamma gamma')
        simpa [Sym2.map_mk, rlc_connectorOuterTargetVertex] using hf
      rw [← SimpleGraph.mem_edgeSet]
      rw [← hedge]
      exact hret.choose.2
    · rw [Sym2.eq_iff] at hf
      simp [rlc_connectorOuterTargetVertex,
        rlc_connectorOuterPort] at hf
  · intro hxy
    let targetEdge : Sym2 (RlcConnectorVertex n) := s(x, y)
    let sourceEdge : Sym2 (Site 2) :=
      rlc_pimsEdgeEquiv (targetEdge.map Subtype.val)
    have hsource : sourceEdge ∈ rlc_connectorEdges gamma gamma' :=
      hxy.2
    have htargetLat : targetEdge.map Subtype.val ∈
        (hypercubicLattice 2).edgeSet := by
      change s((x : Site 2), (y : Site 2)) ∈
        (hypercubicLattice 2).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact hxy.1.1
    have hsourceLat : sourceEdge ∈ (hypercubicLattice 2).edgeSet :=
      rlc_pimsEdgeEquiv_mem_latticeEdge htargetLat
    let lifted := rlc_connectorEdgeLift gamma gamma' sourceEdge hsource
    have hlifted : lifted ∈
        (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
      rlc_connectorEdgeLift_mem_finiteGraph gamma gamma'
        sourceEdge hsource hsourceLat
    let f : Ising.kwg_Edge
        (rlc_connectorAugmentedPlanarDomain gamma gamma') :=
      ⟨lifted, by
        change lifted ∈
          (rlc_connectorFiniteGraph gamma gamma' ⊔
            rlc_connectorTraceWiring gamma gamma').edgeSet
        exact SimpleGraph.edgeSet_mono le_sup_left hlifted⟩
    have hreflected :
        rlc_connectorReflectedDualEdge gamma gamma' f =
          targetEdge.map Subtype.val := by
      apply rlc_pimsEdgeEquiv.injective
      rw [rlc_pimsEdgeEquiv_connectorReflectedDualEdge]
      change lifted.map Subtype.val = sourceEdge
      exact rlc_connectorEdgeLift_map gamma gamma' sourceEdge hsource
    have hret : RlcConnectorRetainedDualEdge gamma gamma' f := by
      refine ⟨⟨targetEdge, ?_⟩, hreflected.symm⟩
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    refine ⟨fun h => hxy.ne
      (rlc_connectorOuterTargetVertex_injective gamma gamma' h), f, ?_⟩
    unfold rlc_connectorOuterDualEdge
    rw [dif_pos hret]
    have hedge : hret.choose.1 = targetEdge := by
      apply rlc_sym2Map_subtypeVal_injective
      exact hret.choose_spec.trans hreflected
    rw [hedge]
    rfl


theorem rlc_connectorOuterSpokeGraph_not_adj_targets {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    ¬(rlc_connectorOuterSpokeGraph gamma gamma').Adj
      (rlc_connectorOuterTargetVertex gamma gamma' x)
      (rlc_connectorOuterTargetVertex gamma gamma' y) := by
  rintro ⟨_, _, hghost⟩
  simp [RlcConnectorOuterIsFace,
    rlc_connectorOuterTargetVertex] at hghost



theorem rlc_connectorOuterDualGraph_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch
      (rlc_connectorPIMSVariableGraph gamma gamma')
      (rlc_connectorOuterDualGraph gamma gamma')
      (rlc_connectorOuterTargetVertex gamma gamma') := by
  intro x y
  rw [rlc_connectorOuterDualGraph, SimpleGraph.sup_adj]
  constructor
  · intro hxy
    exact Or.inl
      ((rlc_connectorOuterRandomGraph_adj_target gamma gamma' x y).2 hxy)
  · rintro (hrandom | hspoke)
    · exact (rlc_connectorOuterRandomGraph_adj_target gamma gamma' x y).1
        hrandom
    · exact (rlc_connectorOuterSpokeGraph_not_adj_targets
        gamma gamma' x y hspoke).elim


def rlc_connectorOuterFaceTag {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorOuterDualVertex gamma gamma' → Bool
  | Sum.inr (Sum.inr _) => true
  | _ => false

@[simp] theorem rlc_connectorOuterFaceTag_eq_true_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    rlc_connectorOuterFaceTag gamma gamma' x = true ↔
      RlcConnectorOuterIsFace gamma gamma' x := by
  rcases x with x | (x | x) <;>
    simp [rlc_connectorOuterFaceTag, RlcConnectorOuterIsFace]


@[simp] theorem rlc_connectorOuterFaceTag_outerDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    (rlc_connectorOuterDualEdge gamma gamma' f).map
        (rlc_connectorOuterFaceTag gamma gamma') = s(false, false) := by
  unfold rlc_connectorOuterDualEdge
  split
  · rename_i hret
    induction hret.choose.1 using Sym2.inductionOn with
    | _ x y =>
        simp [rlc_connectorOuterTargetVertex,
          rlc_connectorOuterFaceTag]
  · simp [rlc_connectorOuterPort, rlc_connectorOuterFaceTag]

theorem rlc_connectorOuterSpoke_faceTag_ne_false {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : (rlc_connectorOuterSpokeGraph gamma gamma').Adj x y) :
    s(x, y).map (rlc_connectorOuterFaceTag gamma gamma') ≠
      s(false, false) := by
  intro htag
  rw [Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_connectorOuterFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_connectorOuterFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  rcases hxy.2.2 with hx | hy
  · have := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [this] at hxfalse
  · have := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [this] at hyfalse


theorem rlc_connectorOuterDualEdge_not_mem_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∉
      (rlc_connectorOuterSpokeGraph gamma gamma').edgeSet := by
  induction hxy : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      intro hspoke
      apply rlc_connectorOuterSpoke_faceTag_ne_false gamma gamma' hspoke
      rw [← hxy]
      exact rlc_connectorOuterFaceTag_outerDualEdge gamma gamma' f




noncomputable def rlc_connectorOuterDualConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorOuterDualVertex gamma gamma')) :=
  fun e => if h : ∃ f, rlc_connectorOuterDualEdge gamma gamma' f = e then
    !(rlc_connectorForceTraceConfig gamma gamma' tau h.choose.1)
  else decide (e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeSet)

@[simp] theorem rlc_connectorOuterDualConfig_randomEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualConfig gamma gamma' tau
        (rlc_connectorOuterDualEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) := by
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i h
    have hf : h.choose = f :=
      rlc_connectorOuterDualEdge_injective gamma gamma' h.choose_spec
    rw [hf]
  · rename_i h
    exact (h ⟨f, rfl⟩).elim



theorem rlc_connectorOuterDualConfig_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (RlcConnectorOuterDualVertex gamma gamma')}
    (he : e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeSet) :
    rlc_connectorOuterDualConfig gamma gamma' tau e = true := by
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i hrandom
    obtain ⟨f, rfl⟩ := hrandom
    exact (rlc_connectorOuterDualEdge_not_mem_spoke
      gamma gamma' f he).elim
  · simp [he]



theorem rlc_connectorOuterFaceProjection_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    (rlc_connectorOuterDualEdge gamma gamma' f).map
        (rlc_connectorOuterFaceProjection gamma gamma') =
      Ising.kwg_dualEnds
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f := by
  unfold rlc_connectorOuterDualEdge
  split
  · rename_i hret
    have hphysical := hret.choose_spec
    have hmapped := congrArg
      (Sym2.map (fun z : Site 2 => BeffaraDC.pfdFace
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm z))) hphysical
    simpa [rlc_connectorOuterTargetVertex,
      rlc_connectorOuterFaceProjection,
      rlc_connectorReflectedDualEdge, Ising.kwg_dualEnds,
      Sym2.map_map] using hmapped
  · simp [rlc_connectorOuterPort,
      rlc_connectorOuterFaceProjection, Ising.kwg_dualEnds,
      BeffaraDC.pfdFace]


noncomputable def rlc_connectorOuterOpenGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    SimpleGraph (RlcConnectorOuterDualVertex gamma gamma') :=
  FK.openSub (rlc_connectorOuterDualGraph gamma gamma')
    (rlc_connectorOuterDualConfig gamma gamma' tau)

noncomputable instance rlc_connectorOuterOpenGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    DecidableRel (rlc_connectorOuterOpenGraph gamma gamma' tau).Adj :=
  Classical.decRel _


theorem rlc_connectorOuterSpoke_le_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorOuterSpokeGraph gamma gamma' ≤
      rlc_connectorOuterOpenGraph gamma gamma' tau := by
  intro x y hxy
  rw [rlc_connectorOuterOpenGraph, FK.openSub_adj]
  refine ⟨Or.inr hxy, ?_⟩
  apply rlc_connectorOuterDualConfig_spoke gamma gamma' tau
  exact (SimpleGraph.mem_edgeSet _).mpr hxy



theorem rlc_connectorOuterDualEdge_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∈
        (rlc_connectorOuterOpenGraph gamma gamma' tau).edgeSet ↔
      f.1 ∉ (FK.openSub
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet := by
  rw [rlc_connectorOuterOpenGraph]
  induction hxy : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      have hrandom :
          (rlc_connectorOuterRandomGraph gamma gamma').Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hxy]
        exact rlc_connectorOuterDualEdge_mem_random gamma gamma' f
      have hconfig :=
        rlc_connectorOuterDualConfig_randomEdge gamma gamma' tau f
      rw [hxy] at hconfig
      rw [hconfig]
      constructor
      · rintro ⟨_, hopen⟩ hprimal
        have htrue :
            rlc_connectorForceTraceConfig gamma gamma' tau f.1 = true := by
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              rw [hfedge] at hprimal
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj] at hprimal
              simpa [hfedge] using hprimal.2
        rw [htrue] at hopen
        simp at hopen
      · intro hclosed
        refine ⟨Or.inl hrandom, ?_⟩
        have hfalse :
            rlc_connectorForceTraceConfig gamma gamma' tau f.1 = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hopen
          apply hclosed
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              have hfmem : f.1 ∈
                  (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeSet :=
                f.2
              rw [hfedge] at hfmem
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
              exact ⟨(SimpleGraph.mem_edgeSet _).mp hfmem,
                by simpa [hfedge] using hopen⟩
        simp [hfalse]




theorem rlc_connectorOuterFaceProjection_reachable_of_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Adj x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable
      (rlc_connectorOuterFaceProjection gamma gamma' x)
      (rlc_connectorOuterFaceProjection gamma gamma' y) := by
  rw [rlc_connectorOuterOpenGraph, FK.openSub_adj] at hxy
  rcases hxy.1 with hrandom | hspoke
  · obtain ⟨f, hf⟩ := hrandom.2
    have hopen : rlc_connectorOuterDualEdge gamma gamma' f ∈
        (rlc_connectorOuterOpenGraph gamma gamma' tau).edgeSet := by
      rw [hf]
      exact (SimpleGraph.mem_edgeSet _).mpr <| by
        rw [rlc_connectorOuterOpenGraph, FK.openSub_adj]
        exact ⟨Or.inl hrandom, hxy.2⟩
    have habsent := (rlc_connectorOuterDualEdge_open_iff
      gamma gamma' tau f).1 hopen
    have hends : Ising.kwg_dualEnds
          (rlc_connectorAugmentedPlanarDomain gamma gamma') f =
        s(rlc_connectorOuterFaceProjection gamma gamma' x,
          rlc_connectorOuterFaceProjection gamma gamma' y) := by
      rw [← rlc_connectorOuterFaceProjection_edge gamma gamma' f, hf,
        Sym2.map_mk]
    by_cases heq : rlc_connectorOuterFaceProjection gamma gamma' x =
        rlc_connectorOuterFaceProjection gamma gamma' y
    · rw [heq]
    · exact ((BeffaraDC.pfdClosedDual_adj
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau)) _ _).2
          ⟨heq, f, habsent, hends⟩).reachable
  · rw [hspoke.2.1]



theorem rlc_connectorOuterFaceProjection_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable
      (rlc_connectorOuterFaceProjection gamma gamma' x)
      (rlc_connectorOuterFaceProjection gamma gamma' y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans
        (rlc_connectorOuterFaceProjection_reachable_of_adj
          gamma gamma' tau hadj)


theorem rlc_connectorOuterDualEdge_endpoints_not_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma'))
    {x y : RlcConnectorOuterDualVertex gamma gamma'}
    (hxy : rlc_connectorOuterDualEdge gamma gamma' f = s(x, y)) :
    ¬RlcConnectorOuterIsFace gamma gamma' x ∧
      ¬RlcConnectorOuterIsFace gamma gamma' y := by
  have htag := rlc_connectorOuterFaceTag_outerDualEdge gamma gamma' f
  rw [hxy, Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_connectorOuterFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_connectorOuterFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  constructor
  · intro hx
    have hxtrue := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [hxtrue] at hxfalse
  · intro hy
    have hytrue := (rlc_connectorOuterFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [hytrue] at hyfalse



theorem rlc_connectorOuterFace_reachable_of_pfd_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {C D : Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Adj C D) :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable
      (rlc_connectorOuterFace gamma gamma' C)
      (rlc_connectorOuterFace gamma gamma' D) := by
  rw [BeffaraDC.pfdClosedDual_adj] at hCD
  obtain ⟨_, f, habsent, hends⟩ := hCD
  have hopen := (rlc_connectorOuterDualEdge_open_iff
    gamma gamma' tau f).2 habsent
  induction hedge : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      have hnonface := rlc_connectorOuterDualEdge_endpoints_not_face
        gamma gamma' f hedge
      have hxface := (rlc_connectorOuterSpoke_le_open gamma gamma' tau
        (rlc_connectorOuterSpoke_adj_face gamma gamma' x hnonface.1)).reachable
      have hyface := (rlc_connectorOuterSpoke_le_open gamma gamma' tau
        (rlc_connectorOuterSpoke_adj_face gamma gamma' y hnonface.2)).reachable
      have hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hedge]
        exact hopen
      have hproj :
          s(rlc_connectorOuterFaceProjection gamma gamma' x,
            rlc_connectorOuterFaceProjection gamma gamma' y) = s(C, D) := by
        rw [← hends, ← rlc_connectorOuterFaceProjection_edge gamma gamma' f,
          hedge, Sym2.map_mk]
      rw [Sym2.eq_iff] at hproj
      rcases hproj with hproj | hproj
      · simpa [hproj.1, hproj.2] using
          hxface.symm.trans (hxy.reachable.trans hyface)
      · simpa [hproj.1, hproj.2] using
          hyface.symm.trans (hxy.symm.reachable.trans hxface)



theorem rlc_connectorOuterFace_reachable_of_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {C D : Ising.kwg_Face
      (rlc_connectorAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable C D) :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable
      (rlc_connectorOuterFace gamma gamma' C)
      (rlc_connectorOuterFace gamma gamma' D) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hCD
  induction hCD with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans (rlc_connectorOuterFace_reachable_of_pfd_adj
        gamma gamma' tau hadj)


theorem rlc_connectorOuter_reachable_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x
      (rlc_connectorOuterFace gamma gamma'
        (rlc_connectorOuterFaceProjection gamma gamma' x)) := by
  by_cases hx : RlcConnectorOuterIsFace gamma gamma' x
  · have heq : x = rlc_connectorOuterFace gamma gamma'
        (rlc_connectorOuterFaceProjection gamma gamma' x) := by
      rcases x with x | (x | x)
      · simp [RlcConnectorOuterIsFace] at hx
      · simp [RlcConnectorOuterIsFace] at hx
      · rfl
    rw [heq]
    rw [rlc_connectorOuterFaceProjection_face]
  · exact (rlc_connectorOuterSpoke_le_open gamma gamma' tau
      (rlc_connectorOuterSpoke_adj_face gamma gamma' x hx)).reachable



theorem rlc_connectorOuter_reachable_iff_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (x y : RlcConnectorOuterDualVertex gamma gamma') :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x y ↔
      (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable
        (rlc_connectorOuterFaceProjection gamma gamma' x)
        (rlc_connectorOuterFaceProjection gamma gamma' y) := by
  constructor
  · exact rlc_connectorOuterFaceProjection_reachable gamma gamma' tau
  · intro hxy
    exact (rlc_connectorOuter_reachable_face gamma gamma' tau x).trans
      ((rlc_connectorOuterFace_reachable_of_pfd gamma gamma' tau hxy).trans
        (rlc_connectorOuter_reachable_face gamma gamma' tau y).symm)


noncomputable def rlc_connectorOuterComponentMap {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).ConnectedComponent →
      (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).ConnectedComponent :=
  ConnectedComponent.lift
    (fun x => (BeffaraDC.pfdClosedDual
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau))).connectedComponentMk
          (rlc_connectorOuterFaceProjection gamma gamma' x))
    (fun _ _ p _ => ConnectedComponent.sound
      (rlc_connectorOuterFaceProjection_reachable gamma gamma' tau
        p.reachable))

@[simp] theorem rlc_connectorOuterComponentMap_mk {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    rlc_connectorOuterComponentMap gamma gamma' tau
        ((rlc_connectorOuterOpenGraph gamma gamma' tau).connectedComponentMk x) =
      (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).connectedComponentMk
        (rlc_connectorOuterFaceProjection gamma gamma' x) :=
  rfl

theorem rlc_connectorOuterComponentMap_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    Function.Injective
      (rlc_connectorOuterComponentMap gamma gamma' tau) := by
  intro A B hAB
  induction A using ConnectedComponent.ind with
  | _ x =>
    induction B using ConnectedComponent.ind with
    | _ y =>
      rw [rlc_connectorOuterComponentMap_mk,
        rlc_connectorOuterComponentMap_mk, ConnectedComponent.eq] at hAB
      exact ConnectedComponent.sound
        ((rlc_connectorOuter_reachable_iff_pfd gamma gamma' tau x y).2 hAB)

theorem rlc_connectorOuterComponentMap_surjective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    Function.Surjective
      (rlc_connectorOuterComponentMap gamma gamma' tau) := by
  intro C
  induction C using ConnectedComponent.ind with
  | _ c =>
    refine ⟨(rlc_connectorOuterOpenGraph gamma gamma' tau).connectedComponentMk
      (rlc_connectorOuterFace gamma gamma' c), ?_⟩
    rw [rlc_connectorOuterComponentMap_mk]
    rfl



noncomputable def rlc_connectorOuterComponentEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    (rlc_connectorOuterOpenGraph gamma gamma' tau).ConnectedComponent ≃
      (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).ConnectedComponent :=
  Equiv.ofBijective (rlc_connectorOuterComponentMap gamma gamma' tau)
    ⟨rlc_connectorOuterComponentMap_injective gamma gamma' tau,
      rlc_connectorOuterComponentMap_surjective gamma gamma' tau⟩


theorem rlc_connectorOuter_numClusters_eq_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorOuterDualGraph gamma gamma') ⊥
        (rlc_connectorOuterDualConfig gamma gamma' tau) =
      Nat.card (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).ConnectedComponent := by
  rw [FK.numClustersBC, sup_bot_eq]
  change Nat.card
      (rlc_connectorOuterOpenGraph gamma gamma' tau).ConnectedComponent = _
  exact Nat.card_congr
    (rlc_connectorOuterComponentEquiv gamma gamma' tau)

theorem rlc_connectorOuterRandom_spoke_disjoint {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset
      (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e hrandom hspoke
  rw [rlc_connectorOuterRandom_edgeFinset] at hrandom
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hrandom
  apply rlc_connectorOuterDualEdge_not_mem_spoke gamma gamma' f
  exact SimpleGraph.mem_edgeFinset.mp hspoke



theorem rlc_openCount_complement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    FK.openCount G (fun e => !(omega e)) =
      G.edgeFinset.card - FK.openCount G omega := by
  have hclosed : FK.openCount G (fun e => !(omega e)) =
      FK.closedCount G omega := by
    unfold FK.openCount FK.closedCount
    congr 1
    ext e
    simp only [Finset.mem_filter]
    cases omega e <;> simp
  rw [hclosed]
  have hsum := FK.openCount_add_closedCount G omega
  omega



theorem rlc_connector_pfdDualEdgeFactor_eq_randomProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    BeffaraDC.edgeProductCount p
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card
        ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card -
          (FK.openSub
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G
            (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet.ncard) =
      ∏ f : Ising.kwg_Edge
          (rlc_connectorAugmentedPlanarDomain gamma gamma'),
        if !(rlc_connectorForceTraceConfig gamma gamma' tau f.1)
          then p else 1 - p := by
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  let forced := rlc_connectorForceTraceConfig gamma gamma' tau
  calc
    BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card - (FK.openSub P.G forced).edgeSet.ncard) =
      BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (FK.openCount P.G (fun e => !(forced e))) := by
          rw [rlc_openCount_complement,
            BeffaraDC.pfd_openSub_edge_ncard]
    _ = FK.edgeProduct P.G p (fun e => !(forced e)) :=
      (BeffaraDC.dlt_edgeProduct_eq_count P.G p
        (fun e => !(forced e))).symm
    _ = ∏ f : Ising.kwg_Edge P,
        if !(forced f.1) then p else 1 - p := by
      unfold FK.edgeProduct
      rw [← Finset.prod_attach P.G.edgeFinset, Finset.attach_eq_univ]
      let edgeEquiv : P.G.edgeFinset ≃ Ising.kwg_Edge P :=
        { toFun := fun e => ⟨e.1, by
            simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          invFun := fun e => ⟨e.1, by
            simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          left_inv := by intro e; rfl
          right_inv := by intro e; rfl }
      apply Fintype.prod_equiv edgeEquiv
      intro f
      simp only [edgeEquiv]
      rfl


theorem rlc_connectorOuter_randomEdgeProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    (∏ e ∈ (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset,
        if rlc_connectorOuterDualConfig gamma gamma' tau e
          then p else 1 - p) =
      ∏ f : Ising.kwg_Edge
          (rlc_connectorAugmentedPlanarDomain gamma gamma'),
        if !(rlc_connectorForceTraceConfig gamma gamma' tau f.1)
          then p else 1 - p := by
  rw [rlc_connectorOuterRandom_edgeFinset,
    Finset.prod_image
      (fun a _ b _ h => rlc_connectorOuterDualEdge_injective gamma gamma' h)]
  apply Finset.prod_congr rfl
  intro f _
  rw [rlc_connectorOuterDualConfig_randomEdge]


theorem rlc_connectorOuter_spokeEdgeProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    (∏ e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset,
        if rlc_connectorOuterDualConfig gamma gamma' tau e
          then p else 1 - p) =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card := by
  calc
    (∏ e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset,
        if rlc_connectorOuterDualConfig gamma gamma' tau e
          then p else 1 - p) =
      ∏ _e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset, p := by
        apply Finset.prod_congr rfl
        intro e he
        rw [rlc_connectorOuterDualConfig_spoke gamma gamma' tau
          (SimpleGraph.mem_edgeFinset.mp he)]
        rfl
    _ = p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card := by
      simp


theorem rlc_connectorOuter_edgeProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    FK.edgeProduct (rlc_connectorOuterDualGraph gamma gamma') p
        (rlc_connectorOuterDualConfig gamma gamma' tau) =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card *
        BeffaraDC.edgeProductCount p
          (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card
          ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card -
            (FK.openSub
              (rlc_connectorAugmentedPlanarDomain gamma gamma').G
              (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet.ncard) := by
  have hEdges : (rlc_connectorOuterDualGraph gamma gamma').edgeFinset =
      (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset ∪
        (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset := by
    ext e
    simp [rlc_connectorOuterDualGraph, SimpleGraph.mem_edgeFinset]
  unfold FK.edgeProduct
  rw [hEdges,
    Finset.prod_union (rlc_connectorOuterRandom_spoke_disjoint gamma gamma'),
    rlc_connectorOuter_randomEdgeProduct,
    ← rlc_connector_pfdDualEdgeFactor_eq_randomProduct,
    rlc_connectorOuter_spokeEdgeProduct]
  ring



theorem rlc_connectorOuter_bcWeight_eq_pfdDualWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p q : Real) :
    FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
        (rlc_connectorOuterDualConfig gamma gamma' tau) =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card *
        BeffaraDC.pfdDualWeight
          (rlc_connectorAugmentedPlanarDomain gamma gamma') p q
          (FK.openSub
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G
            (rlc_connectorForceTraceConfig gamma gamma' tau)) := by
  unfold FK.bcWeight BeffaraDC.pfdDualWeight
  rw [rlc_connectorOuter_edgeProduct,
    rlc_connectorOuter_numClusters_eq_pfd]
  ring



noncomputable def rlc_connectorOuterRestrictedZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
      (rlc_connectorOuterDualConfig gamma gamma' tau)


noncomputable def rlc_connectorOuterRestrictedProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Real :=
  FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
      (rlc_connectorOuterDualConfig gamma gamma' tau) /
    rlc_connectorOuterRestrictedZ gamma gamma' p q



theorem rlc_connectorOuterRestrictedZ_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorOuterRestrictedZ gamma gamma' p q =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card *
        rlc_connectorForcedDualZ gamma gamma' p q := by
  unfold rlc_connectorOuterRestrictedZ rlc_connectorForcedDualZ
  simp_rw [rlc_connectorOuter_bcWeight_eq_pfdDualWeight]
  rw [Finset.mul_sum]



theorem rlc_connectorOuterRestrictedProb_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) :
    rlc_connectorOuterRestrictedProb gamma gamma' p q tau =
      rlc_connectorForcedDualProb gamma gamma' p q tau := by
  unfold rlc_connectorOuterRestrictedProb rlc_connectorForcedDualProb
  rw [rlc_connectorOuter_bcWeight_eq_pfdDualWeight,
    rlc_connectorOuterRestrictedZ_eq]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hp.ne')

theorem rlc_connector_path_end_mem_vertices {a b c d : Int}
    (gamma : RlcCrossingPath a b c d) :
    (gamma.2.1 : Site 2) ∈ rlc_pathVertices gamma := by
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
  exact ⟨⟨gamma.2.1, rightSide_subset gamma.2.1.2⟩,
    gamma.2.2.1.end_mem_support, rfl⟩


def rlc_connectorRightAnchor {n : Int} (gamma : RlcRightDiagonalPath n) :
    RlcConnectorVertex n :=
  ⟨gamma.1.1, rlc_rightPathVertex_mem_connectorBox gamma
    (rlc_path_start_mem_vertices gamma.1)⟩


def rlc_connectorLeftAnchor {n : Int} (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorVertex n :=
  ⟨gamma'.1.2.1, rlc_leftPathVertex_mem_connectorBox gamma'
    (rlc_connector_path_end_mem_vertices gamma'.1)⟩

@[simp] theorem rlc_connectorRightAnchor_onRight {n : Int}
    (gamma : RlcRightDiagonalPath n) :
    rlc_connectorOnRight gamma (rlc_connectorRightAnchor gamma) :=
  rlc_path_start_mem_vertices gamma.1

@[simp] theorem rlc_connectorLeftAnchor_onLeft {n : Int}
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorOnLeft gamma' (rlc_connectorLeftAnchor gamma') :=
  rlc_connector_path_end_mem_vertices gamma'.1



def rlc_connectorMergedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) :=
  rlc_connectorSeparateWiring gamma gamma' ⊔
    SimpleGraph.edge (rlc_connectorRightAnchor gamma)
      (rlc_connectorLeftAnchor gamma')

noncomputable instance rlc_connectorMergedWiring_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorMergedWiring gamma gamma').Adj :=
  Classical.decRel _





def RlcConnectorInnerCore {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorVertex n) : Prop :=
  x = rlc_connectorRightAnchor gamma ∨
    x = rlc_connectorLeftAnchor gamma' ∨
      x ∈ (rlc_connectorPIMSVariableGraph gamma gamma').support

noncomputable instance rlc_connectorInnerCoreDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (RlcConnectorInnerCore gamma gamma') :=
  Classical.decPred _


abbrev RlcConnectorInnerVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {x : RlcConnectorVertex n // RlcConnectorInnerCore gamma gamma' x}

noncomputable instance rlc_connectorInnerVertexFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcConnectorInnerVertex gamma gamma') :=
  Fintype.ofFinite _

noncomputable instance rlc_connectorInnerVertexDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcConnectorInnerVertex gamma gamma') :=
  Classical.decEq _


noncomputable def rlc_connectorInnerGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  (rlc_connectorPIMSVariableGraph gamma gamma').comap Subtype.val

noncomputable instance rlc_connectorInnerGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorInnerGraph gamma gamma').Adj :=
  Classical.decRel _


def rlc_connectorInnerOuterVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorInnerVertex gamma gamma' →
      RlcConnectorOuterDualVertex gamma gamma' :=
  fun x => rlc_connectorOuterTargetVertex gamma gamma' x.1

theorem rlc_connectorInnerOuterVertex_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_connectorInnerOuterVertex gamma gamma') := by
  intro x y hxy
  apply Subtype.ext
  exact rlc_connectorOuterTargetVertex_injective gamma gamma' hxy


theorem rlc_connectorInnerOuter_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch (rlc_connectorInnerGraph gamma gamma')
      (rlc_connectorOuterDualGraph gamma gamma')
      (rlc_connectorInnerOuterVertex gamma gamma') := by
  intro x y
  exact rlc_connectorOuterDualGraph_adjMatch gamma gamma' x.1 y.1


def rlc_connectorInnerRightAnchor {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorInnerVertex gamma gamma' :=
  ⟨rlc_connectorRightAnchor gamma, Or.inl rfl⟩


def rlc_connectorInnerLeftAnchor {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorInnerVertex gamma gamma' :=
  ⟨rlc_connectorLeftAnchor gamma', Or.inr (Or.inl rfl)⟩


noncomputable def rlc_connectorInnerSeparateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  (rlc_connectorSeparateWiring gamma gamma').comap Subtype.val

noncomputable instance rlc_connectorInnerSeparateWiringDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorInnerSeparateWiring gamma gamma').Adj :=
  Classical.decRel _


noncomputable def rlc_connectorInnerMergedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  (rlc_connectorMergedWiring gamma gamma').comap Subtype.val

noncomputable instance rlc_connectorInnerMergedWiringDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorInnerMergedWiring gamma gamma').Adj :=
  Classical.decRel _


def rlc_connectorInnerEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorInnerVertex gamma gamma'))) :=
  {omega | (FK.openSub (rlc_connectorInnerGraph gamma gamma') omega ⊔
      rlc_connectorInnerSeparateWiring gamma gamma').Reachable
        (rlc_connectorInnerRightAnchor gamma gamma')
        (rlc_connectorInnerLeftAnchor gamma gamma')}



noncomputable def rlc_connectorInnerInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  FK.ocd_inducedWiring (rlc_connectorOuterDualGraph gamma gamma')
    (rlc_connectorInnerOuterVertex gamma gamma') (fun _ => False) psi

noncomputable instance rlc_connectorInnerInducedWiringDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))) :
    DecidableRel (rlc_connectorInnerInducedWiring gamma gamma' psi).Adj :=
  Classical.decRel _




theorem rlc_connectorInner_outerWeight_factorization {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma')))
    (p q : Real) :
    FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma')
          psi omega) =
      FK.bcWeight (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerInducedWiring gamma gamma' psi) p q omega *
        FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma')
          (rlc_connectorInnerOuterVertex gamma gamma')
          (fun _ => False) psi p q := by
  simpa [rlc_connectorInnerInducedWiring] using
    (FK.ocd_bcWeight_psiExt
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerOuterVertex_injective gamma gamma')
      (rlc_connectorInnerOuter_adjMatch gamma gamma')
      (p := p) (q := q) psi omega)


theorem rlc_connectorInner_condProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma'))) :
    FK.condBcProb (rlc_connectorOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_connectorInnerOuterVertex gamma gamma')) psi
        (FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma')
          psi omega) =
      FK.bcProb (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma' psi) p q omega := by
  simpa [rlc_connectorInnerInducedWiring] using
    (FK.ocd_condBcProb_psiExt_eq_bcProb
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerOuterVertex_injective gamma gamma')
      (rlc_connectorInnerOuter_adjMatch gamma gamma')
      hp hp1 hq psi omega)


def rlc_connectorInnerEdgeToVariable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorInnerGraph gamma gamma').edgeSet →
      (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet :=
  fun e => ⟨e.1.map Subtype.val, by
    induction heq : e.1 using Sym2.inductionOn with
    | _ x y =>
        have he := e.2
        rw [heq, SimpleGraph.mem_edgeSet] at he
        rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
        exact he⟩

theorem rlc_connectorInnerEdgeToVariable_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorInnerEdgeToVariable gamma gamma') := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val hef)

theorem rlc_connectorInnerEdgeToVariable_surjective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Surjective
      (rlc_connectorInnerEdgeToVariable gamma gamma') := by
  intro e
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y :=
        by
          have he := e.2
          rw [heq, SimpleGraph.mem_edgeSet] at he
          exact he
      let xc : RlcConnectorInnerVertex gamma gamma' :=
        ⟨x, Or.inr (Or.inr hxy.mem_support_left)⟩
      let yc : RlcConnectorInnerVertex gamma gamma' :=
        ⟨y, Or.inr (Or.inr hxy.mem_support_right)⟩
      let a : (rlc_connectorInnerGraph gamma gamma').edgeSet :=
        ⟨s(xc, yc), by
          rw [SimpleGraph.mem_edgeSet]
          exact hxy⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change s(x, y) = e.1
      exact heq.symm


noncomputable def rlc_connectorInnerVariableEdgeEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorInnerGraph gamma gamma').edgeSet ≃
      (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet :=
  Equiv.ofBijective (rlc_connectorInnerEdgeToVariable gamma gamma')
    ⟨rlc_connectorInnerEdgeToVariable_injective gamma gamma',
      rlc_connectorInnerEdgeToVariable_surjective gamma gamma'⟩

theorem rlc_connectorVariableEdge_preimage_mem_connector {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet) :
    rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma' := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      simpa [heq, Sym2.map_mk] using he.2

theorem rlc_connectorVariableEdge_map_mem_lattice {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet) :
    e.1.map Subtype.val ∈ (hypercubicLattice 2).edgeSet := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact he.1.1



noncomputable def rlc_connectorVariableSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet →
      (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
  fun e =>
    let source := rlc_pimsEdgeEquiv (e.1.map Subtype.val)
    let hsource : source ∈ rlc_connectorEdges gamma gamma' :=
      rlc_connectorVariableEdge_preimage_mem_connector gamma gamma' e
    ⟨rlc_connectorEdgeLift gamma gamma' source hsource,
      rlc_connectorEdgeLift_mem_finiteGraph gamma gamma' source hsource
        (rlc_pimsEdgeEquiv_mem_latticeEdge
          (rlc_connectorVariableEdge_map_mem_lattice gamma gamma' e))⟩

theorem rlc_connectorVariableSourceEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorVariableSourceEdge gamma gamma') := by
  intro e f hef
  apply Subtype.ext
  apply rlc_sym2Map_subtypeVal_injective
  apply rlc_pimsEdgeEquiv.injective
  have hlift := congrArg
    (fun a : (rlc_connectorFiniteGraph gamma gamma').edgeSet =>
      a.1.map Subtype.val) hef
  simpa [rlc_connectorVariableSourceEdge] using hlift



noncomputable def rlc_connectorInnerSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorInnerGraph gamma gamma').edgeSet →
      (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
  (rlc_connectorVariableSourceEdge gamma gamma') ∘
    (rlc_connectorInnerVariableEdgeEquiv gamma gamma')

theorem rlc_connectorInnerSourceEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_connectorInnerSourceEdge gamma gamma') :=
  (rlc_connectorVariableSourceEdge_injective gamma gamma').comp
    (rlc_connectorInnerVariableEdgeEquiv gamma gamma').injective


abbrev RlcConnectorOuterSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorFiniteGraph gamma gamma').edgeSet //
    e ∉ Set.range (rlc_connectorInnerSourceEdge gamma gamma')}

noncomputable instance rlc_connectorOuterSourceEdgeFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcConnectorOuterSourceEdge gamma gamma') :=
  Fintype.ofFinite _

noncomputable instance rlc_connectorOuterSourceEdgeDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcConnectorOuterSourceEdge gamma gamma') :=
  Classical.decEq _



def rlc_connectorInnerActiveOfSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet :=
  fun e => !(tau (rlc_connectorInnerSourceEdge gamma gamma' e))


def rlc_connectorOuterActiveOfSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma') :=
  fun e => tau e.1



noncomputable def rlc_connectorSourceActiveAssemble {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (pair : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet ×
      ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
  fun e => if h : e ∈ Set.range
      (rlc_connectorInnerSourceEdge gamma gamma') then
    !(pair.1 h.choose)
  else pair.2 ⟨e, h⟩

@[simp] theorem rlc_connectorSourceActiveAssemble_inner {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi)
        (rlc_connectorInnerSourceEdge gamma gamma' e) = !(eta e) := by
  unfold rlc_connectorSourceActiveAssemble
  split
  · rename_i h
    have he : h.choose = e :=
      rlc_connectorInnerSourceEdge_injective gamma gamma' h.choose_spec
    rw [he]
  · rename_i h
    exact (h ⟨e, rfl⟩).elim

@[simp] theorem rlc_connectorSourceActiveAssemble_outer {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'))
    (e : RlcConnectorOuterSourceEdge gamma gamma') :
    rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi) e.1 = xi e := by
  unfold rlc_connectorSourceActiveAssemble
  rw [dif_neg e.2]



noncomputable def rlc_connectorSourceActiveEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet ≃
      ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet ×
        ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma') where
  toFun tau := (rlc_connectorInnerActiveOfSource gamma gamma' tau,
    rlc_connectorOuterActiveOfSource gamma gamma' tau)
  invFun := rlc_connectorSourceActiveAssemble gamma gamma'
  left_inv tau := by
    funext e
    unfold rlc_connectorSourceActiveAssemble
    split
    · rename_i h
      have he : rlc_connectorInnerSourceEdge gamma gamma' h.choose = e :=
        h.choose_spec
      simp [rlc_connectorInnerActiveOfSource, he]
    · rename_i h
      rfl
  right_inv pair := by
    rcases pair with ⟨eta, xi⟩
    apply Prod.ext
    · funext e
      simp [rlc_connectorInnerActiveOfSource]
    · funext e
      simp [rlc_connectorOuterActiveOfSource]

theorem rlc_connectorForceTraceConfig_finiteEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorForceTraceConfig gamma gamma' tau e.1 = tau e.1 := by
  unfold rlc_connectorForceTraceConfig
  rw [if_neg]
  intro htrace
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have hefinite := e.2
      rw [heq] at hefinite htrace
      exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma'
        ((SimpleGraph.mem_edgeSet _).mp hefinite)
        ((SimpleGraph.mem_edgeSet _).mp
          (SimpleGraph.mem_edgeFinset.mp htrace))

theorem rlc_connectorVariableSourceEdge_map {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet) :
    (rlc_connectorVariableSourceEdge gamma gamma' e).1.map Subtype.val =
      rlc_pimsEdgeEquiv (e.1.map Subtype.val) := by
  change (rlc_connectorEdgeLift gamma gamma'
      (rlc_pimsEdgeEquiv (e.1.map Subtype.val))
      (rlc_connectorVariableEdge_preimage_mem_connector
        gamma gamma' e)).map Subtype.val = _
  exact rlc_connectorEdgeLift_map gamma gamma' _
    (rlc_connectorVariableEdge_preimage_mem_connector gamma gamma' e)

theorem rlc_connectorInnerSourceEdge_map {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    (rlc_connectorInnerSourceEdge gamma gamma' e).1.map Subtype.val =
      rlc_pimsEdgeEquiv
        ((rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map
          Subtype.val) := by
  change (rlc_connectorVariableSourceEdge gamma gamma'
      (rlc_connectorInnerVariableEdgeEquiv gamma gamma' e)).1.map
        Subtype.val = _
  rw [show rlc_connectorInnerVariableEdgeEquiv gamma gamma' e =
      rlc_connectorInnerEdgeToVariable gamma gamma' e from rfl]
  exact rlc_connectorVariableSourceEdge_map gamma gamma' _


noncomputable def rlc_connectorInnerAugmentedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma') :=
  ⟨(rlc_connectorInnerSourceEdge gamma gamma' e).1,
    SimpleGraph.edgeSet_mono le_sup_left
      (rlc_connectorInnerSourceEdge gamma gamma' e).2⟩



theorem rlc_connectorOuterDualEdge_innerAugmented {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorOuterDualEdge gamma gamma'
        (rlc_connectorInnerAugmentedEdge gamma gamma' e) =
      e.1.map (rlc_connectorInnerOuterVertex gamma gamma') := by
  let v := rlc_connectorInnerEdgeToVariable gamma gamma' e
  let f := rlc_connectorInnerAugmentedEdge gamma gamma' e
  have hreflected : rlc_connectorReflectedDualEdge gamma gamma' f =
      v.1.map Subtype.val := by
    apply rlc_pimsEdgeEquiv.injective
    rw [rlc_pimsEdgeEquiv_connectorReflectedDualEdge]
    change (rlc_connectorInnerSourceEdge gamma gamma' e).1.map
      Subtype.val = rlc_pimsEdgeEquiv (v.1.map Subtype.val)
    exact rlc_connectorInnerSourceEdge_map gamma gamma' e
  have hret : RlcConnectorRetainedDualEdge gamma gamma' f :=
    ⟨v, hreflected.symm⟩
  unfold rlc_connectorOuterDualEdge
  rw [dif_pos hret]
  have hedge : hret.choose.1 = v.1 := by
    apply rlc_sym2Map_subtypeVal_injective
    exact hret.choose_spec.trans hreflected
  rw [hedge]
  simp [v, rlc_connectorInnerEdgeToVariable,
    rlc_connectorInnerOuterVertex, Sym2.map_map]

theorem rlc_connectorReflectedDualEdge_innerAugmented {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorReflectedDualEdge gamma gamma'
        (rlc_connectorInnerAugmentedEdge gamma gamma' e) =
      (rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map
        Subtype.val := by
  apply rlc_pimsEdgeEquiv.injective
  rw [rlc_pimsEdgeEquiv_connectorReflectedDualEdge]
  exact rlc_connectorInnerSourceEdge_map gamma gamma' e



theorem rlc_connectorOuterDualEdge_mem_innerRange_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∈
        Set.range (FK.ocd_innerEdge
          (rlc_connectorInnerOuterVertex gamma gamma')) ↔
      ∃ e : (rlc_connectorInnerGraph gamma gamma').edgeSet,
        f.1 = (rlc_connectorInnerSourceEdge gamma gamma' e).1 := by
  constructor
  · rintro ⟨a, ha⟩
    induction a using Sym2.inductionOn with
    | _ x y =>
      have ha' : rlc_connectorOuterDualEdge gamma gamma' f =
          s(rlc_connectorInnerOuterVertex gamma gamma' x,
            rlc_connectorInnerOuterVertex gamma gamma' y) := by
        simpa [FK.ocd_innerEdge, Sym2.map_mk] using ha.symm
      have houter : (rlc_connectorOuterDualGraph gamma gamma').Adj
          (rlc_connectorInnerOuterVertex gamma gamma' x)
          (rlc_connectorInnerOuterVertex gamma gamma' y) := by
        rw [rlc_connectorOuterDualGraph, SimpleGraph.sup_adj]
        left
        refine ⟨?_, f, ha'⟩
        intro hxy
        have : x = y :=
          rlc_connectorInnerOuterVertex_injective gamma gamma' hxy
        subst y
        exact rlc_connectorOuterDualEdge_ne_diag gamma gamma' f _ ha'
      have hinner : (rlc_connectorInnerGraph gamma gamma').Adj x y :=
        (rlc_connectorInnerOuter_adjMatch gamma gamma' x y).mpr houter
      let e : (rlc_connectorInnerGraph gamma gamma').edgeSet :=
        ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hinner⟩
      have hreflected : rlc_connectorReflectedDualEdge gamma gamma' f =
          (rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map
            Subtype.val := by
        unfold rlc_connectorOuterDualEdge at ha'
        split at ha'
        · rename_i hret
          have hedge : hret.choose.1 =
              (rlc_connectorInnerEdgeToVariable gamma gamma' e).1 := by
            apply Sym2.map.injective
              (rlc_connectorOuterTargetVertex_injective gamma gamma')
            simpa [e, rlc_connectorInnerEdgeToVariable,
              rlc_connectorInnerOuterVertex, Sym2.map_map] using ha'
          exact hret.choose_spec.symm.trans <| by rw [hedge]
        · rw [Sym2.eq_iff] at ha'
          simp [rlc_connectorInnerOuterVertex,
            rlc_connectorOuterTargetVertex,
            rlc_connectorOuterPort] at ha'
      have hf : f = rlc_connectorInnerAugmentedEdge gamma gamma' e :=
        rlc_connectorReflectedDualEdge_injective gamma gamma'
          (hreflected.trans
            (rlc_connectorReflectedDualEdge_innerAugmented
              gamma gamma' e).symm)
      exact ⟨e, congrArg Subtype.val hf⟩
  · rintro ⟨e, he⟩
    have hf : f = rlc_connectorInnerAugmentedEdge gamma gamma' e := by
      apply Subtype.ext
      exact he
    rw [hf, rlc_connectorOuterDualEdge_innerAugmented]
    exact ⟨e.1, rfl⟩



theorem rlc_connectorOuterConfig_innerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_connectorInnerOuterVertex gamma gamma')
          (rlc_connectorOuterDualConfig gamma gamma' tau)) e =
      rlc_connectorInnerActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) e := by
  unfold FK.restrictActive FK.ocd_innerRestrict
  change rlc_connectorOuterDualConfig gamma gamma' tau
      (e.1.map (rlc_connectorInnerOuterVertex gamma gamma')) = _
  rw [← rlc_connectorOuterDualEdge_innerAugmented gamma gamma' e,
    rlc_connectorOuterDualConfig_randomEdge]
  rw [show (rlc_connectorInnerAugmentedEdge gamma gamma' e).1 =
      (rlc_connectorInnerSourceEdge gamma gamma' e).1 from rfl,
    rlc_connectorForceTraceConfig_finiteEdge]
  rfl



noncomputable def rlc_connectorSplitSourceConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  FK.extendActive (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi))

theorem rlc_connectorOuterConfig_agreesOff_of_outerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau sigma : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (houter : rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) =
      rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') sigma)) :
    FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerOuterVertex gamma gamma'))
      (rlc_connectorOuterDualConfig gamma gamma' tau)
      (rlc_connectorOuterDualConfig gamma gamma' sigma) := by
  intro a ha
  have haRange : a ∉ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerOuterVertex gamma gamma')) := by
    rwa [FK.ocd_mem_innerEdgeFinset] at ha
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i hrandom
    let f := hrandom.choose
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
      have hfmem := f.2
      rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
      change (rlc_connectorFiniteGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
      rcases hfmem with hfinite | htrace
      · let ef : (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
          ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hfinite⟩
        have heq : f.1 = ef.1 := hedge
        have hef : ef ∉ Set.range
            (rlc_connectorInnerSourceEdge gamma gamma') := by
          intro hmem
          obtain ⟨e, he⟩ := hmem
          apply haRange
          rw [← hrandom.choose_spec]
          apply (rlc_connectorOuterDualEdge_mem_innerRange_iff
            gamma gamma' f).2
          refine ⟨e, ?_⟩
          calc
            f.1 = ef.1 := heq
            _ = (rlc_connectorInnerSourceEdge gamma gamma' e).1 :=
              (congrArg Subtype.val he).symm
        have hcoord := congrFun houter ⟨ef, hef⟩
        simp only [rlc_connectorOuterActiveOfSource,
          FK.restrictActive] at hcoord
        have htau := rlc_connectorForceTraceConfig_finiteEdge
          gamma gamma' tau ef
        have hsigma := rlc_connectorForceTraceConfig_finiteEdge
          gamma gamma' sigma ef
        have htau' : rlc_connectorForceTraceConfig gamma gamma' tau
            s(x, y) = tau s(x, y) := by simpa [ef] using htau
        have hsigma' : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = sigma s(x, y) := by simpa [ef] using hsigma
        have hforce : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = rlc_connectorForceTraceConfig gamma gamma' tau
              s(x, y) := hsigma'.trans (hcoord.symm.trans htau'.symm)
        exact congrArg Bool.not hforce
      · have hmem : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr htrace)
        have htau : rlc_connectorForceTraceConfig gamma gamma' tau
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos hmem
        have hsigma : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos hmem
        exact congrArg Bool.not (hsigma.trans htau.symm)
  · rfl



theorem rlc_connectorSplitSource_outProj_independent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta eta' : ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma')
        (rlc_connectorOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma')
        (rlc_connectorOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta' xi)) := by
  let tau := rlc_connectorSplitSourceConfig gamma gamma' eta xi
  let sigma := rlc_connectorSplitSourceConfig gamma gamma' eta' xi
  have hagree : FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerOuterVertex gamma gamma'))
      (rlc_connectorOuterDualConfig gamma gamma' tau)
      (rlc_connectorOuterDualConfig gamma gamma' sigma) :=
    rlc_connectorOuterConfig_agreesOff_of_outerActive
      gamma gamma' tau sigma (by
        funext e
        simp [tau, sigma, rlc_connectorSplitSourceConfig,
          rlc_connectorOuterActiveOfSource])
  unfold FK.AgreesOff at hagree
  funext a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerOuterVertex gamma gamma'))
  · rw [FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerOuterVertex_injective gamma gamma') _ ha]
  · rw [FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact (hagree a (by
      rw [FK.ocd_mem_innerEdgeFinset]
      exact ha)).symm

theorem rlc_connectorEmptyBoundary_eq_bot {V : Type*}
    [Fintype V] [DecidableEq V] :
    Lattice.boundaryCliqueGraph (fun _ : V => False) =
      (⊥ : SimpleGraph V) := by
  ext x y
  rw [Lattice.boundaryCliqueGraph_adj]
  simp

theorem rlc_connector_bcWeight_emptyBoundary_eq_bot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : Real) (omega : ConfigSpace (Sym2 V)) :
    FK.bcWeight G (Lattice.boundaryCliqueGraph (fun _ : V => False))
        p q omega =
      FK.bcWeight G ⊥ p q omega := by
  unfold FK.bcWeight FK.numClustersBC
  rw [rlc_connectorEmptyBoundary_eq_bot]



noncomputable def rlc_connectorOuterStateOfSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    ConfigSpace (Sym2 (RlcConnectorOuterDualVertex gamma gamma')) :=
  FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma')
    (rlc_connectorOuterDualConfig gamma gamma'
      (rlc_connectorSplitSourceConfig gamma gamma'
        (fun _ => false) xi))

theorem rlc_connectorSplitSource_outProj_eq_state {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma')
        (rlc_connectorOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      rlc_connectorOuterStateOfSource gamma gamma' xi := by
  exact rlc_connectorSplitSource_outProj_independent
    gamma gamma' eta (fun _ => false) xi

theorem rlc_connectorOuterState_reconstruct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma')
        (rlc_connectorOuterStateOfSource gamma gamma' xi)
        (FK.ocd_innerRestrict (rlc_connectorInnerOuterVertex gamma gamma')
          (rlc_connectorOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      rlc_connectorOuterDualConfig gamma gamma'
        (rlc_connectorSplitSourceConfig gamma gamma' eta xi) := by
  let rho := rlc_connectorOuterDualConfig gamma gamma'
    (rlc_connectorSplitSourceConfig gamma gamma' eta xi)
  have hstate : rlc_connectorOuterStateOfSource gamma gamma' xi =
      FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma') rho :=
    (rlc_connectorSplitSource_outProj_eq_state
      gamma gamma' eta xi).symm
  rw [hstate]
  apply FK.ocd_psiExt_innerRestrict_of_agreesOff
    (rlc_connectorInnerOuterVertex_injective gamma gamma')
  intro a ha
  rw [FK.ocd_mem_innerEdgeFinset] at ha
  exact (FK.ocd_outProj_eq_of_not_range rho ha).symm

theorem rlc_connectorSplitSource_innerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.restrictActive (rlc_connectorInnerGraph gamma gamma')
        (FK.ocd_innerRestrict (rlc_connectorInnerOuterVertex gamma gamma')
          (rlc_connectorOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) = eta := by
  funext e
  rw [rlc_connectorOuterConfig_innerActive]
  rw [show FK.restrictActive (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSplitSourceConfig gamma gamma' eta xi) =
        rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi) by
    unfold rlc_connectorSplitSourceConfig
    exact FK.restrictActive_extendActive _ _]
  have h := congrArg Prod.fst
    ((rlc_connectorSourceActiveEquiv gamma gamma').right_inv (eta, xi))
  exact congrFun h e



theorem rlc_connectorSplitSource_outerWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'))
    (p q : Real) :
    FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
        (rlc_connectorOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      FK.activeBCWeight (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerInducedWiring gamma gamma'
            (rlc_connectorOuterStateOfSource gamma gamma' xi))
          (fun _ => p) q eta *
        FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma')
          (rlc_connectorInnerOuterVertex gamma gamma')
          (fun _ => False)
          (rlc_connectorOuterStateOfSource gamma gamma' xi) p q := by
  let rho := rlc_connectorOuterDualConfig gamma gamma'
    (rlc_connectorSplitSourceConfig gamma gamma' eta xi)
  let psi := rlc_connectorOuterStateOfSource gamma gamma' xi
  let omega := FK.ocd_innerRestrict
    (rlc_connectorInnerOuterVertex gamma gamma') rho
  have hfactor := rlc_connectorInner_outerWeight_factorization
    gamma gamma' psi omega p q
  have hreconstruct := rlc_connectorOuterState_reconstruct
    gamma gamma' eta xi
  change FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma')
    psi omega = rho at hreconstruct
  rw [hreconstruct] at hfactor
  rw [rlc_connector_bcWeight_emptyBoundary_eq_bot] at hfactor
  rw [hfactor]
  congr 1
  unfold FK.activeBCWeight
  apply FK.bcWeight_eq_of_edges
  intro e he
  have heSet : e ∈ (rlc_connectorInnerGraph gamma gamma').edgeSet := by
    rwa [← SimpleGraph.mem_edgeFinset]
  let a : (rlc_connectorInnerGraph gamma gamma').edgeSet := ⟨e, heSet⟩
  calc
    omega e = FK.restrictActive
        (rlc_connectorInnerGraph gamma gamma') omega a := rfl
    _ = eta a := congrFun
      (rlc_connectorSplitSource_innerActive gamma gamma' eta xi) a
    _ = FK.extendActive (rlc_connectorInnerGraph gamma gamma') eta e :=
      (FK.extendActive_apply
        (rlc_connectorInnerGraph gamma gamma') eta a).symm



noncomputable def rlc_connectorFibreMixtureZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
    FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma')
        (rlc_connectorInnerOuterVertex gamma gamma')
        (fun _ => False)
        (rlc_connectorOuterStateOfSource gamma gamma' xi) p q *
      FK.activeBCZ (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma'
          (rlc_connectorOuterStateOfSource gamma gamma' xi))
        (fun _ => p) q

theorem rlc_connectorFibreMixtureZ_eq_sum_outerWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorFibreMixtureZ gamma gamma' p q =
      ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
        ∑ eta : ConfigSpace
            (rlc_connectorInnerGraph gamma gamma').edgeSet,
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) := by
  unfold rlc_connectorFibreMixtureZ FK.activeBCZ
  apply Finset.sum_congr rfl
  intro xi _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorSplitSource_outerWeight]
  ring


noncomputable def rlc_connectorFibreWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) : Real :=
  (FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma')
        (rlc_connectorInnerOuterVertex gamma gamma')
        (fun _ => False)
        (rlc_connectorOuterStateOfSource gamma gamma' xi) p q *
      FK.activeBCZ (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma'
          (rlc_connectorOuterStateOfSource gamma gamma' xi))
        (fun _ => p) q) /
    rlc_connectorFibreMixtureZ gamma gamma' p q

theorem rlc_connectorFibreMixtureZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_connectorFibreMixtureZ gamma gamma' p q := by
  unfold rlc_connectorFibreMixtureZ
  apply Finset.sum_pos
  · intro xi _
    exact mul_pos
      (FK.ocd_psiShift_pos
        (Gout := rlc_connectorOuterDualGraph gamma gamma')
        (ιV := rlc_connectorInnerOuterVertex gamma gamma')
        (bdryOut := fun _ => False) hp hp1 hq)
      (FK.activeBCZ_pos
        (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma'
          (rlc_connectorOuterStateOfSource gamma gamma' xi))
        (fun _ => hp) (fun _ => hp1) hq)
  · exact Finset.univ_nonempty

theorem rlc_connectorFibreWeight_nonneg {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    0 ≤ rlc_connectorFibreWeight gamma gamma' p q xi := by
  unfold rlc_connectorFibreWeight
  exact div_nonneg
    (mul_nonneg
      (FK.ocd_psiShift_pos
        (Gout := rlc_connectorOuterDualGraph gamma gamma')
        (ιV := rlc_connectorInnerOuterVertex gamma gamma')
        (bdryOut := fun _ => False) hp hp1 hq).le
      (FK.activeBCZ_pos
        (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma'
          (rlc_connectorOuterStateOfSource gamma gamma' xi))
        (fun _ => hp) (fun _ => hp1) hq).le)
    (rlc_connectorFibreMixtureZ_pos gamma gamma' hp hp1 hq).le

theorem rlc_connectorFibreWeight_sum_eq_one {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
      rlc_connectorFibreWeight gamma gamma' p q xi = 1 := by
  unfold rlc_connectorFibreWeight rlc_connectorFibreMixtureZ
  rw [← Finset.sum_div]
  exact div_self (rlc_connectorFibreMixtureZ_pos
    gamma gamma' hp hp1 hq).ne'


noncomputable def rlc_connectorSplitOuterEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) : Real :=
  (∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
      ∑ eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet,
        A.indicator (fun _ => (1 : Real)) eta *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) /
    rlc_connectorFibreMixtureZ gamma gamma' p q


theorem rlc_connectorSplitOuterEventMass_eq_fibreMixture {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorSplitOuterEventMass gamma gamma' p q A =
      ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
        rlc_connectorFibreWeight gamma gamma' p q xi *
          FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
            (rlc_connectorInnerInducedWiring gamma gamma'
              (rlc_connectorOuterStateOfSource gamma gamma' xi))
            (fun _ => p) q A := by
  unfold rlc_connectorSplitOuterEventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro xi _
  rw [show (∑ eta,
      A.indicator (fun _ => (1 : Real)) eta *
        FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma')
          (rlc_connectorInnerOuterVertex gamma gamma')
          (fun _ => False)
          (rlc_connectorOuterStateOfSource gamma gamma' xi) p q *
        FK.activeBCNumer (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerInducedWiring gamma gamma'
            (rlc_connectorOuterStateOfSource gamma gamma' xi))
          (fun _ => p) q (A.indicator fun _ => (1 : Real)) by
    unfold FK.activeBCNumer
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eta _
    rw [rlc_connectorSplitSource_outerWeight]
    ring]
  unfold rlc_connectorFibreWeight FK.activeBCProbOf
  rw [FK.activeBCMean_eq_div]
  have hZi := (FK.activeBCZ_pos
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerInducedWiring gamma gamma'
      (rlc_connectorOuterStateOfSource gamma gamma' xi))
    (fun _ => hp) (fun _ => hp1) hq).ne'
  field_simp


theorem rlc_connectorForceTraceConfig_activeCanonical {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorForceTraceConfig gamma gamma' tau f.1 =
      rlc_connectorForceTraceConfig gamma gamma'
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma')
          (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau))
        f.1 := by
  unfold rlc_connectorForceTraceConfig
  split
  · rfl
  · rename_i hnot
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
      have hf := f.2
      rw [hedge, SimpleGraph.mem_edgeSet] at hf
      change (rlc_connectorFiniteGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y at hf
      rcases hf with hfinite | htrace
      · let e : (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
          ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hfinite⟩
        exact (FK.extendActive_apply
          (rlc_connectorFiniteGraph gamma gamma')
          (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau)
          e).symm
      · apply (hnot ?_).elim
        rw [hedge]
        exact SimpleGraph.mem_edgeFinset.mpr
          ((SimpleGraph.mem_edgeSet _).mpr htrace)



theorem rlc_connectorOuterDualConfig_activeCanonical {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorOuterDualConfig gamma gamma' tau =
      rlc_connectorOuterDualConfig gamma gamma'
        (FK.extendActive (rlc_connectorFiniteGraph gamma gamma')
          (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau)) := by
  funext a
  unfold rlc_connectorOuterDualConfig
  split
  · rename_i h
    rw [rlc_connectorForceTraceConfig_activeCanonical
      gamma gamma' tau h.choose]
  · rfl



theorem rlc_connectorOuterRestrictedZ_eq_inactive_mul_fibreMixture {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorOuterRestrictedZ gamma gamma' p q =
      2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
        rlc_connectorFibreMixtureZ gamma gamma' p q := by
  unfold rlc_connectorOuterRestrictedZ
  rw [← Equiv.sum_comp
    (FK.activeSplitEquiv (rlc_connectorFiniteGraph gamma gamma')).symm,
    Fintype.sum_prod_type]
  have hinactive : forall eta : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 (RlcConnectorVertex n) //
          e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeSet},
        FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorOuterDualConfig gamma gamma'
            ((FK.activeSplitEquiv
              (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)))) =
        2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              (FK.extendActive
                (rlc_connectorFiniteGraph gamma gamma') eta)) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      have hconfig : rlc_connectorOuterDualConfig gamma gamma'
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          rlc_connectorOuterDualConfig gamma gamma'
            (FK.extendActive
              (rlc_connectorFiniteGraph gamma gamma') eta) := by
        rw [rlc_connectorOuterDualConfig_activeCanonical,
          FK.restrictActive_activeSplitEquiv_symm]
      exact congrArg
        (FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q)
        hconfig),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      FK.card_inactive_config]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => hinactive eta),
    ← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp
    (rlc_connectorSourceActiveEquiv gamma gamma').symm,
    Fintype.sum_prod_type, Finset.sum_comm,
    rlc_connectorFibreMixtureZ_eq_sum_outerWeight]
  rfl



def rlc_connectorReducedStateOfConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet :=
  rlc_connectorInnerActiveOfSource gamma gamma'
    (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau)



theorem rlc_connectorOuterReducedNumer_eq_inactive_mul_splitNumer {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    (∑ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
            (fun _ => (1 : Real)) tau *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma' tau)) =
      2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
        (∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
          ∑ eta : ConfigSpace
              (rlc_connectorInnerGraph gamma gamma').edgeSet,
            A.indicator (fun _ => (1 : Real)) eta *
              FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
                (rlc_connectorOuterDualConfig gamma gamma'
                  (rlc_connectorSplitSourceConfig
                    gamma gamma' eta xi))) := by
  rw [← Equiv.sum_comp
    (FK.activeSplitEquiv (rlc_connectorFiniteGraph gamma gamma')).symm,
    Fintype.sum_prod_type]
  have hinactive : forall eta : ConfigSpace
      (rlc_connectorFiniteGraph gamma gamma').edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 (RlcConnectorVertex n) //
          e ∉ (rlc_connectorFiniteGraph gamma gamma').edgeSet},
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
            (fun _ => (1 : Real))
            ((FK.activeSplitEquiv
              (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              ((FK.activeSplitEquiv
                (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)))) =
        2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') *
          (A.indicator (fun _ => (1 : Real))
              (rlc_connectorInnerActiveOfSource gamma gamma' eta) *
            FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
              (rlc_connectorOuterDualConfig gamma gamma'
                (FK.extendActive
                  (rlc_connectorFiniteGraph gamma gamma') eta))) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      have hactive : rlc_connectorReducedStateOfConfig gamma gamma'
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          rlc_connectorInnerActiveOfSource gamma gamma' eta := by
        simp only [rlc_connectorReducedStateOfConfig,
          FK.restrictActive_activeSplitEquiv_symm]
      have hconfig : rlc_connectorOuterDualConfig gamma gamma'
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          rlc_connectorOuterDualConfig gamma gamma'
            (FK.extendActive
              (rlc_connectorFiniteGraph gamma gamma') eta) := by
        rw [rlc_connectorOuterDualConfig_activeCanonical,
          FK.restrictActive_activeSplitEquiv_symm]
      have hindicator :
          (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
          (fun _ => (1 : Real))
          ((FK.activeSplitEquiv
            (rlc_connectorFiniteGraph gamma gamma')).symm (eta, xi)) =
          A.indicator (fun _ => (1 : Real))
            (rlc_connectorInnerActiveOfSource gamma gamma' eta) := by
        calc
          _ = A.indicator (fun _ => (1 : Real))
              (rlc_connectorReducedStateOfConfig gamma gamma'
                ((FK.activeSplitEquiv
                  (rlc_connectorFiniteGraph gamma gamma')).symm
                    (eta, xi))) := by
            simpa only [Function.comp_apply] using
              (Set.indicator_comp_right
                (rlc_connectorReducedStateOfConfig gamma gamma')
                (s := A) (g := fun _ => (1 : Real)))
          _ = _ := by rw [hactive]
      exact congrArg₂ (fun a b : Real => a * b) hindicator
        (congrArg
          (FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q)
          hconfig)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      FK.card_inactive_config]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => hinactive eta),
    ← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp
    (rlc_connectorSourceActiveEquiv gamma gamma').symm,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi _
  apply Finset.sum_congr rfl
  intro eta _
  have hpair := (rlc_connectorSourceActiveEquiv gamma gamma').right_inv
    (eta, xi)
  have hinner := congrArg Prod.fst hpair
  rw [show rlc_connectorInnerActiveOfSource gamma gamma'
      ((rlc_connectorSourceActiveEquiv gamma gamma').symm (eta, xi)) =
        eta by exact hinner]
  rfl



theorem rlc_connectorForcedDualReducedEventMass_eq_split {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A) =
      rlc_connectorSplitOuterEventMass gamma gamma' p q A := by
  unfold rlc_connectorForcedDualEventMass
  simp_rw [← rlc_connectorOuterRestrictedProb_eq_forcedDualProb
    gamma gamma' _ hp]
  unfold rlc_connectorOuterRestrictedProb
  rw [show (∑ x,
      (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
          (fun _ => (1 : Real)) x *
        (FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorOuterDualConfig gamma gamma' x) /
            rlc_connectorOuterRestrictedZ gamma gamma' p q)) =
      ∑ x,
        ((rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator
            (fun _ => (1 : Real)) x *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma' x)) /
          rlc_connectorOuterRestrictedZ gamma gamma' p q by
    apply Finset.sum_congr rfl
    intro x _
    ring,
    ← Finset.sum_div,
    rlc_connectorOuterReducedNumer_eq_inactive_mul_splitNumer,
    rlc_connectorOuterRestrictedZ_eq_inactive_mul_fibreMixture]
  unfold rlc_connectorSplitOuterEventMass
  have htwo : (2 : Real) ^
      FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') ≠ 0 := by
    positivity
  exact mul_div_mul_left _ _ htwo



noncomputable def rlc_connectorOuterMaxConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (Sym2 (RlcConnectorOuterDualVertex gamma gamma')) :=
  rlc_connectorOuterDualConfig gamma gamma' (fun _ => false)


theorem rlc_connectorOuterDualConfig_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorOuterDualConfig gamma gamma' tau ≤
      rlc_connectorOuterMaxConfig gamma gamma' := by
  intro a
  unfold rlc_connectorOuterMaxConfig rlc_connectorOuterDualConfig
  split
  · rename_i h
    unfold rlc_connectorForceTraceConfig
    split
    · rfl
    · cases tau h.choose.1 <;> simp
  · exact le_rfl


noncomputable def rlc_connectorInnerMaxInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  rlc_connectorInnerInducedWiring gamma gamma'
    (rlc_connectorOuterMaxConfig gamma gamma')

noncomputable instance rlc_connectorInnerMaxInducedWiringDecidableAdj
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_connectorInnerMaxInducedWiring gamma gamma').Adj :=
  Classical.decRel _


theorem rlc_connectorInnerInducedWiring_mono {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {psi phi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))}
    (hpsi : psi ≤ phi) :
    rlc_connectorInnerInducedWiring gamma gamma' psi ≤
      rlc_connectorInnerInducedWiring gamma gamma' phi := by
  intro x y hxy
  refine ⟨hxy.1, hxy.2.mono ?_⟩
  intro u v huv
  rw [FK.ocd_outsideGraph_adj] at huv ⊢
  rcases huv with hopen | hboundary
  · exact Or.inl ⟨hopen.1, hpsi _ hopen.2.1, hopen.2.2⟩
  · exact Or.inr hboundary



theorem rlc_connectorInnerInducedWiring_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorInnerInducedWiring gamma gamma'
        (rlc_connectorOuterDualConfig gamma gamma' tau) ≤
      rlc_connectorInnerMaxInducedWiring gamma gamma' := by
  exact rlc_connectorInnerInducedWiring_mono gamma gamma'
    (rlc_connectorOuterDualConfig_le_max gamma gamma' tau)





abbrev RlcConnectorCollaredOuterVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  RlcConnectorVertex n ⊕
    ((Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma') × Bool) ⊕
      Ising.kwg_Face (rlc_connectorCollaredPlanarDomain gamma gamma'))

noncomputable instance rlc_connectorCollaredOuterVertexFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcConnectorCollaredOuterVertex gamma gamma') := by
  letI : Fintype (Ising.kwg_Face
      (rlc_connectorCollaredPlanarDomain gamma gamma')) :=
    Fintype.ofFinite _
  infer_instance

noncomputable instance rlc_connectorCollaredOuterVertexDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcConnectorCollaredOuterVertex gamma gamma') :=
  Classical.decEq _

def rlc_connectorCollaredOuterTargetVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorVertex n → RlcConnectorCollaredOuterVertex gamma gamma' :=
  Sum.inl

def rlc_connectorCollaredOuterPort {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) (side : Bool) :
    RlcConnectorCollaredOuterVertex gamma gamma' :=
  Sum.inr (Sum.inl (f, side))

def rlc_connectorCollaredOuterFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorCollaredPlanarDomain gamma gamma')) :
    RlcConnectorCollaredOuterVertex gamma gamma' :=
  Sum.inr (Sum.inr C)

theorem rlc_connectorCollaredOuterTargetVertex_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorCollaredOuterTargetVertex gamma gamma') :=
  Sum.inl_injective



noncomputable def rlc_connectorCollaredOuterDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    Sym2 (RlcConnectorCollaredOuterVertex gamma gamma') :=
  if h : RlcConnectorRetainedDualEdge gamma gamma' f then
    h.choose.1.map
      (rlc_connectorCollaredOuterTargetVertex gamma gamma')
  else
    s(rlc_connectorCollaredOuterPort gamma gamma' f false,
      rlc_connectorCollaredOuterPort gamma gamma' f true)

theorem rlc_connectorCollaredOuterDualEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorCollaredOuterDualEdge gamma gamma') := by
  intro f g hfg
  unfold rlc_connectorCollaredOuterDualEdge at hfg
  split at hfg <;> split at hfg
  · rename_i hf hg
    have hedge : hf.choose.1 = hg.choose.1 := by
      apply Sym2.map.injective
        (rlc_connectorCollaredOuterTargetVertex_injective gamma gamma')
      exact hfg
    apply rlc_connectorReflectedDualEdge_injective gamma gamma'
    rw [← hf.choose_spec, ← hg.choose_spec, hedge]
  · rename_i hf hg
    revert hfg
    induction hf.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_connectorCollaredOuterTargetVertex,
          rlc_connectorCollaredOuterPort] at hfg
  · rename_i hf hg
    revert hfg
    induction hg.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_connectorCollaredOuterTargetVertex,
          rlc_connectorCollaredOuterPort] at hfg
  · simpa [rlc_connectorCollaredOuterPort, Sym2.eq_iff] using hfg



noncomputable def rlc_connectorCollaredOuterFaceProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorCollaredOuterVertex gamma gamma' →
      Ising.kwg_Face (rlc_connectorCollaredPlanarDomain gamma gamma')
  | Sum.inl x => BeffaraDC.pfdFace
      (rlc_connectorCollaredPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)
  | Sum.inr (Sum.inl (f, false)) => BeffaraDC.pfdFace
      (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankLeft
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inl (f, true)) => BeffaraDC.pfdFace
      (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankRight
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inr C) => C

def RlcConnectorCollaredOuterIsFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorCollaredOuterVertex gamma gamma' → Prop
  | Sum.inr (Sum.inr _) => True
  | _ => False

noncomputable instance rlc_connectorCollaredOuterIsFaceDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (RlcConnectorCollaredOuterIsFace gamma gamma') :=
  Classical.decPred _

noncomputable def rlc_connectorCollaredOuterSpokeGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorCollaredOuterVertex gamma gamma') where
  Adj x y := x ≠ y ∧
    rlc_connectorCollaredOuterFaceProjection gamma gamma' x =
      rlc_connectorCollaredOuterFaceProjection gamma gamma' y ∧
    (RlcConnectorCollaredOuterIsFace gamma gamma' x ∨
      RlcConnectorCollaredOuterIsFace gamma gamma' y)
  symm := by
    rintro x y ⟨hne, hface, hghost⟩
    exact ⟨hne.symm, hface.symm, hghost.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance rlc_connectorCollaredOuterSpokeGraphDecidableAdj
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_connectorCollaredOuterSpokeGraph gamma gamma').Adj :=
  Classical.decRel _

noncomputable def rlc_connectorCollaredOuterRandomGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorCollaredOuterVertex gamma gamma') where
  Adj x y := x ≠ y ∧ ∃ f,
    rlc_connectorCollaredOuterDualEdge gamma gamma' f = s(x, y)
  symm := by
    rintro x y ⟨hne, f, hf⟩
    exact ⟨hne.symm, f, hf.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable def rlc_connectorCollaredOuterDualGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorCollaredOuterVertex gamma gamma') :=
  rlc_connectorCollaredOuterRandomGraph gamma gamma' ⊔
    rlc_connectorCollaredOuterSpokeGraph gamma gamma'

noncomputable instance rlc_connectorCollaredOuterDualGraphDecidableAdj
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_connectorCollaredOuterDualGraph gamma gamma').Adj :=
  Classical.decRel _



noncomputable def rlc_connectorCollaredOuterDualConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')) :=
  fun e => if h : ∃ f,
      rlc_connectorCollaredOuterDualEdge gamma gamma' f = e then
    !(rlc_connectorForceTraceConfig gamma gamma' tau h.choose.1)
  else decide
    (e ∈ (rlc_connectorCollaredOuterSpokeGraph gamma gamma').edgeSet)


noncomputable def rlc_connectorCollaredDualEnds {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    Sym2 (Ising.kwg_Face
      (rlc_connectorCollaredPlanarDomain gamma gamma')) :=
  s(BeffaraDC.pfdFace (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankLeft
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f),
    BeffaraDC.pfdFace (rlc_connectorCollaredPlanarDomain gamma gamma')
      (Ising.kwg_flankRight
        (rlc_connectorAugmentedPlanarDomain gamma gamma') f))



theorem rlc_connectorCollaredOuterFaceProjection_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    (rlc_connectorCollaredOuterDualEdge gamma gamma' f).map
        (rlc_connectorCollaredOuterFaceProjection gamma gamma') =
      rlc_connectorCollaredDualEnds gamma gamma' f := by
  unfold rlc_connectorCollaredOuterDualEdge
  split
  · rename_i hret
    have hphysical := hret.choose_spec
    have hmapped := congrArg
      (Sym2.map (fun z : Site 2 => BeffaraDC.pfdFace
        (rlc_connectorCollaredPlanarDomain gamma gamma')
        (rlc_dualReflect.symm z))) hphysical
    simpa [rlc_connectorCollaredOuterTargetVertex,
      rlc_connectorCollaredOuterFaceProjection,
      rlc_connectorReflectedDualEdge,
      rlc_connectorCollaredDualEnds, Sym2.map_map] using hmapped
  · simp [rlc_connectorCollaredOuterPort,
      rlc_connectorCollaredOuterFaceProjection,
      rlc_connectorCollaredDualEnds]

theorem rlc_connectorCollaredOuterRandomGraph_adj_target {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_connectorCollaredOuterRandomGraph gamma gamma').Adj
        (rlc_connectorCollaredOuterTargetVertex gamma gamma' x)
        (rlc_connectorCollaredOuterTargetVertex gamma gamma' y) ↔
      (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y := by
  constructor
  · rintro ⟨_, f, hf⟩
    unfold rlc_connectorCollaredOuterDualEdge at hf
    split at hf
    · rename_i hret
      have hedge : hret.choose.1 = s(x, y) := by
        apply Sym2.map.injective
          (rlc_connectorCollaredOuterTargetVertex_injective gamma gamma')
        simpa [Sym2.map_mk,
          rlc_connectorCollaredOuterTargetVertex] using hf
      rw [← SimpleGraph.mem_edgeSet, ← hedge]
      exact hret.choose.2
    · rw [Sym2.eq_iff] at hf
      simp [rlc_connectorCollaredOuterTargetVertex,
        rlc_connectorCollaredOuterPort] at hf
  · intro hxy
    let targetEdge : Sym2 (RlcConnectorVertex n) := s(x, y)
    let sourceEdge : Sym2 (Site 2) :=
      rlc_pimsEdgeEquiv (targetEdge.map Subtype.val)
    have hsource : sourceEdge ∈ rlc_connectorEdges gamma gamma' :=
      hxy.2
    have htargetLat : targetEdge.map Subtype.val ∈
        (hypercubicLattice 2).edgeSet := by
      change s((x : Site 2), (y : Site 2)) ∈
        (hypercubicLattice 2).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact hxy.1.1
    have hsourceLat : sourceEdge ∈ (hypercubicLattice 2).edgeSet :=
      rlc_pimsEdgeEquiv_mem_latticeEdge htargetLat
    let lifted := rlc_connectorEdgeLift gamma gamma' sourceEdge hsource
    have hlifted : lifted ∈
        (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
      rlc_connectorEdgeLift_mem_finiteGraph gamma gamma'
        sourceEdge hsource hsourceLat
    let f : Ising.kwg_Edge
        (rlc_connectorAugmentedPlanarDomain gamma gamma') :=
      ⟨lifted, SimpleGraph.edgeSet_mono le_sup_left hlifted⟩
    have hreflected :
        rlc_connectorReflectedDualEdge gamma gamma' f =
          targetEdge.map Subtype.val := by
      apply rlc_pimsEdgeEquiv.injective
      rw [rlc_pimsEdgeEquiv_connectorReflectedDualEdge]
      change lifted.map Subtype.val = sourceEdge
      exact rlc_connectorEdgeLift_map gamma gamma' sourceEdge hsource
    have hret : RlcConnectorRetainedDualEdge gamma gamma' f := by
      refine ⟨⟨targetEdge, ?_⟩, hreflected.symm⟩
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    refine ⟨fun h => hxy.ne
      (rlc_connectorCollaredOuterTargetVertex_injective
        gamma gamma' h), f, ?_⟩
    unfold rlc_connectorCollaredOuterDualEdge
    rw [dif_pos hret]
    have hedge : hret.choose.1 = targetEdge := by
      apply rlc_sym2Map_subtypeVal_injective
      exact hret.choose_spec.trans hreflected
    rw [hedge]
    rfl

theorem rlc_connectorCollaredOuterSpokeGraph_not_adj_targets {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    ¬(rlc_connectorCollaredOuterSpokeGraph gamma gamma').Adj
      (rlc_connectorCollaredOuterTargetVertex gamma gamma' x)
      (rlc_connectorCollaredOuterTargetVertex gamma gamma' y) := by
  rintro ⟨_, _, hghost⟩
  simp [RlcConnectorCollaredOuterIsFace,
    rlc_connectorCollaredOuterTargetVertex] at hghost



theorem rlc_connectorCollaredOuterDualGraph_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch
      (rlc_connectorPIMSVariableGraph gamma gamma')
      (rlc_connectorCollaredOuterDualGraph gamma gamma')
      (rlc_connectorCollaredOuterTargetVertex gamma gamma') := by
  intro x y
  rw [rlc_connectorCollaredOuterDualGraph, SimpleGraph.sup_adj]
  constructor
  · intro hxy
    exact Or.inl
      ((rlc_connectorCollaredOuterRandomGraph_adj_target
        gamma gamma' x y).2 hxy)
  · rintro (hrandom | hspoke)
    · exact (rlc_connectorCollaredOuterRandomGraph_adj_target
        gamma gamma' x y).1 hrandom
    · exact (rlc_connectorCollaredOuterSpokeGraph_not_adj_targets
        gamma gamma' x y hspoke).elim

def rlc_connectorInnerCollaredOuterVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorInnerVertex gamma gamma' →
      RlcConnectorCollaredOuterVertex gamma gamma' :=
  fun x => rlc_connectorCollaredOuterTargetVertex gamma gamma' x.1

theorem rlc_connectorInnerCollaredOuterVertex_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorInnerCollaredOuterVertex gamma gamma') := by
  intro x y hxy
  apply Subtype.ext
  exact rlc_connectorCollaredOuterTargetVertex_injective
    gamma gamma' hxy

theorem rlc_connectorInnerCollaredOuter_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch (rlc_connectorInnerGraph gamma gamma')
      (rlc_connectorCollaredOuterDualGraph gamma gamma')
      (rlc_connectorInnerCollaredOuterVertex gamma gamma') := by
  intro x y
  exact rlc_connectorCollaredOuterDualGraph_adjMatch
    gamma gamma' x.1 y.1

noncomputable def rlc_connectorInnerCollaredInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma'))) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  FK.ocd_inducedWiring
    (rlc_connectorCollaredOuterDualGraph gamma gamma')
    (rlc_connectorInnerCollaredOuterVertex gamma gamma')
    (fun _ => False) psi

noncomputable instance rlc_connectorInnerCollaredInducedWiringDecidableAdj
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma'))) :
    DecidableRel
      (rlc_connectorInnerCollaredInducedWiring gamma gamma' psi).Adj :=
  Classical.decRel _



theorem rlc_connectorInnerCollared_outerWeight_factorization {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma')))
    (p q : Real) :
    FK.bcWeight (rlc_connectorCollaredOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_psiExt
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          psi omega) =
      FK.bcWeight (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerCollaredInducedWiring gamma gamma' psi)
          p q omega *
        FK.ocd_psiShift
          (rlc_connectorCollaredOuterDualGraph gamma gamma')
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (fun _ => False) psi p q := by
  simpa [rlc_connectorInnerCollaredInducedWiring] using
    (FK.ocd_bcWeight_psiExt
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorCollaredOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerCollaredOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma')
      (rlc_connectorInnerCollaredOuter_adjMatch gamma gamma')
      (p := p) (q := q) psi omega)


theorem rlc_connectorInnerCollared_condProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma'))) :
    FK.condBcProb (rlc_connectorCollaredOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')) psi
        (FK.ocd_psiExt
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          psi omega) =
      FK.bcProb (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerCollaredInducedWiring gamma gamma' psi)
        p q omega := by
  simpa [rlc_connectorInnerCollaredInducedWiring] using
    (FK.ocd_condBcProb_psiExt_eq_bcProb
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorCollaredOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerCollaredOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma')
      (rlc_connectorInnerCollaredOuter_adjMatch gamma gamma')
      hp hp1 hq psi omega)



theorem rlc_connectorCollaredOuterDualEdge_innerAugmented {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    rlc_connectorCollaredOuterDualEdge gamma gamma'
        (rlc_connectorInnerAugmentedEdge gamma gamma' e) =
      e.1.map (rlc_connectorInnerCollaredOuterVertex gamma gamma') := by
  let v := rlc_connectorInnerEdgeToVariable gamma gamma' e
  let f := rlc_connectorInnerAugmentedEdge gamma gamma' e
  have hreflected : rlc_connectorReflectedDualEdge gamma gamma' f =
      v.1.map Subtype.val := by
    exact rlc_connectorReflectedDualEdge_innerAugmented gamma gamma' e
  have hret : RlcConnectorRetainedDualEdge gamma gamma' f :=
    ⟨v, hreflected.symm⟩
  unfold rlc_connectorCollaredOuterDualEdge
  rw [dif_pos hret]
  have hedge : hret.choose.1 = v.1 := by
    apply rlc_sym2Map_subtypeVal_injective
    exact hret.choose_spec.trans hreflected
  rw [hedge]
  simp [v, rlc_connectorInnerEdgeToVariable,
    rlc_connectorInnerCollaredOuterVertex,
    rlc_connectorCollaredOuterTargetVertex, Sym2.map_map]

@[simp] theorem rlc_connectorCollaredOuterDualConfig_randomEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorCollaredOuterDualConfig gamma gamma' tau
        (rlc_connectorCollaredOuterDualEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) := by
  unfold rlc_connectorCollaredOuterDualConfig
  split
  · rename_i h
    have hf : h.choose = f :=
      rlc_connectorCollaredOuterDualEdge_injective
        gamma gamma' h.choose_spec
    rw [hf]
  · rename_i h
    exact (h ⟨f, rfl⟩).elim



theorem rlc_connectorCollaredOuterConfig_innerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    FK.restrictActive (rlc_connectorInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (rlc_connectorCollaredOuterDualConfig gamma gamma' tau)) e =
      rlc_connectorInnerActiveOfSource gamma gamma'
        (FK.restrictActive
          (rlc_connectorFiniteGraph gamma gamma') tau) e := by
  unfold FK.restrictActive FK.ocd_innerRestrict
  change rlc_connectorCollaredOuterDualConfig gamma gamma' tau
      (e.1.map
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')) = _
  rw [← rlc_connectorCollaredOuterDualEdge_innerAugmented
      gamma gamma' e,
    rlc_connectorCollaredOuterDualConfig_randomEdge]
  rw [show (rlc_connectorInnerAugmentedEdge gamma gamma' e).1 =
      (rlc_connectorInnerSourceEdge gamma gamma' e).1 from rfl,
    rlc_connectorForceTraceConfig_finiteEdge]
  rfl



theorem rlc_connectorCollaredOuterDualEdge_mem_innerRange_of_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma'))
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (he : f.1 = (rlc_connectorInnerSourceEdge gamma gamma' e).1) :
    rlc_connectorCollaredOuterDualEdge gamma gamma' f ∈
      Set.range (FK.ocd_innerEdge
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')) := by
  have hf : f = rlc_connectorInnerAugmentedEdge gamma gamma' e := by
    apply Subtype.ext
    exact he
  rw [hf, rlc_connectorCollaredOuterDualEdge_innerAugmented]
  exact ⟨e.1, rfl⟩



theorem rlc_connectorCollaredOuterConfig_agreesOff_of_outerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau sigma : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (houter : rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) =
      rlc_connectorOuterActiveOfSource gamma gamma'
        (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') sigma)) :
    FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerCollaredOuterVertex gamma gamma'))
      (rlc_connectorCollaredOuterDualConfig gamma gamma' tau)
      (rlc_connectorCollaredOuterDualConfig gamma gamma' sigma) := by
  intro a ha
  have haRange : a ∉ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerCollaredOuterVertex gamma gamma')) := by
    rwa [FK.ocd_mem_innerEdgeFinset] at ha
  unfold rlc_connectorCollaredOuterDualConfig
  split
  · rename_i hrandom
    let f := hrandom.choose
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
      have hfmem := f.2
      rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
      change (rlc_connectorFiniteGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
      rcases hfmem with hfinite | htrace
      · let ef : (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
          ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hfinite⟩
        have heq : f.1 = ef.1 := hedge
        have hef : ef ∉ Set.range
            (rlc_connectorInnerSourceEdge gamma gamma') := by
          intro hmem
          obtain ⟨e, he⟩ := hmem
          apply haRange
          rw [← hrandom.choose_spec]
          apply rlc_connectorCollaredOuterDualEdge_mem_innerRange_of_source
            gamma gamma' f e
          calc
            f.1 = ef.1 := heq
            _ = (rlc_connectorInnerSourceEdge gamma gamma' e).1 :=
              (congrArg Subtype.val he).symm
        have hcoord := congrFun houter ⟨ef, hef⟩
        simp only [rlc_connectorOuterActiveOfSource,
          FK.restrictActive] at hcoord
        have htau := rlc_connectorForceTraceConfig_finiteEdge
          gamma gamma' tau ef
        have hsigma := rlc_connectorForceTraceConfig_finiteEdge
          gamma gamma' sigma ef
        have htau' : rlc_connectorForceTraceConfig gamma gamma' tau
            s(x, y) = tau s(x, y) := by simpa [ef] using htau
        have hsigma' : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = sigma s(x, y) := by simpa [ef] using hsigma
        have hforce : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = rlc_connectorForceTraceConfig gamma gamma' tau
              s(x, y) := hsigma'.trans (hcoord.symm.trans htau'.symm)
        exact congrArg Bool.not hforce
      · have hmem : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr htrace)
        have htau : rlc_connectorForceTraceConfig gamma gamma' tau
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos hmem
        have hsigma : rlc_connectorForceTraceConfig gamma gamma' sigma
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos hmem
        exact congrArg Bool.not (hsigma.trans htau.symm)
  · rfl

theorem rlc_connectorCollaredSplitSource_outProj_independent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta eta' : ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      FK.ocd_outProj
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta' xi)) := by
  let tau := rlc_connectorSplitSourceConfig gamma gamma' eta xi
  let sigma := rlc_connectorSplitSourceConfig gamma gamma' eta' xi
  have hagree : FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_connectorInnerCollaredOuterVertex gamma gamma'))
      (rlc_connectorCollaredOuterDualConfig gamma gamma' tau)
      (rlc_connectorCollaredOuterDualConfig gamma gamma' sigma) :=
    rlc_connectorCollaredOuterConfig_agreesOff_of_outerActive
      gamma gamma' tau sigma (by
        funext e
        simp [tau, sigma, rlc_connectorSplitSourceConfig,
          rlc_connectorOuterActiveOfSource])
  unfold FK.AgreesOff at hagree
  funext a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_connectorInnerCollaredOuterVertex gamma gamma'))
  · rw [FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
      (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma') _ ha]
  · rw [FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact (hagree a (by
      rw [FK.ocd_mem_innerEdgeFinset]
      exact ha)).symm

noncomputable def rlc_connectorCollaredOuterStateOfSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')) :=
  FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma')
    (rlc_connectorCollaredOuterDualConfig gamma gamma'
      (rlc_connectorSplitSourceConfig gamma gamma'
        (fun _ => false) xi))

theorem rlc_connectorCollaredSplitSource_outProj_eq_state {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      rlc_connectorCollaredOuterStateOfSource gamma gamma' xi := by
  exact rlc_connectorCollaredSplitSource_outProj_independent
    gamma gamma' eta (fun _ => false) xi

theorem rlc_connectorCollaredOuterState_reconstruct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.ocd_psiExt
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)
        (FK.ocd_innerRestrict
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (rlc_connectorCollaredOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      rlc_connectorCollaredOuterDualConfig gamma gamma'
        (rlc_connectorSplitSourceConfig gamma gamma' eta xi) := by
  let rho := rlc_connectorCollaredOuterDualConfig gamma gamma'
    (rlc_connectorSplitSourceConfig gamma gamma' eta xi)
  have hstate : rlc_connectorCollaredOuterStateOfSource gamma gamma' xi =
      FK.ocd_outProj
        (rlc_connectorInnerCollaredOuterVertex gamma gamma') rho :=
    (rlc_connectorCollaredSplitSource_outProj_eq_state
      gamma gamma' eta xi).symm
  rw [hstate]
  apply FK.ocd_psiExt_innerRestrict_of_agreesOff
    (rlc_connectorInnerCollaredOuterVertex_injective gamma gamma')
  intro a ha
  rw [FK.ocd_mem_innerEdgeFinset] at ha
  exact (FK.ocd_outProj_eq_of_not_range rho ha).symm

theorem rlc_connectorCollaredSplitSource_innerActive {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    FK.restrictActive (rlc_connectorInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (rlc_connectorCollaredOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      eta := by
  funext e
  rw [rlc_connectorCollaredOuterConfig_innerActive]
  rw [show FK.restrictActive (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorSplitSourceConfig gamma gamma' eta xi) =
        rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi) by
    unfold rlc_connectorSplitSourceConfig
    exact FK.restrictActive_extendActive _ _]
  have h := congrArg Prod.fst
    ((rlc_connectorSourceActiveEquiv gamma gamma').right_inv (eta, xi))
  exact congrFun h e


theorem rlc_connectorCollaredSplitSource_outerWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'))
    (p q : Real) :
    FK.bcWeight (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q
        (rlc_connectorCollaredOuterDualConfig gamma gamma'
          (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) =
      FK.activeBCWeight (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerCollaredInducedWiring gamma gamma'
            (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
          (fun _ => p) q eta *
        FK.ocd_psiShift
          (rlc_connectorCollaredOuterDualGraph gamma gamma')
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (fun _ => False)
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)
          p q := by
  let rho := rlc_connectorCollaredOuterDualConfig gamma gamma'
    (rlc_connectorSplitSourceConfig gamma gamma' eta xi)
  let psi := rlc_connectorCollaredOuterStateOfSource gamma gamma' xi
  let omega := FK.ocd_innerRestrict
    (rlc_connectorInnerCollaredOuterVertex gamma gamma') rho
  have hfactor := rlc_connectorInnerCollared_outerWeight_factorization
    gamma gamma' psi omega p q
  have hreconstruct := rlc_connectorCollaredOuterState_reconstruct
    gamma gamma' eta xi
  change FK.ocd_psiExt
    (rlc_connectorInnerCollaredOuterVertex gamma gamma')
    psi omega = rho at hreconstruct
  rw [hreconstruct] at hfactor
  rw [rlc_connector_bcWeight_emptyBoundary_eq_bot] at hfactor
  rw [hfactor]
  congr 1
  unfold FK.activeBCWeight
  apply FK.bcWeight_eq_of_edges
  intro e he
  have heSet : e ∈ (rlc_connectorInnerGraph gamma gamma').edgeSet := by
    rwa [← SimpleGraph.mem_edgeFinset]
  let a : (rlc_connectorInnerGraph gamma gamma').edgeSet := ⟨e, heSet⟩
  calc
    omega e = FK.restrictActive
        (rlc_connectorInnerGraph gamma gamma') omega a := rfl
    _ = eta a := congrFun
      (rlc_connectorCollaredSplitSource_innerActive
        gamma gamma' eta xi) a
    _ = FK.extendActive (rlc_connectorInnerGraph gamma gamma') eta e :=
      (FK.extendActive_apply
        (rlc_connectorInnerGraph gamma gamma') eta a).symm

noncomputable def rlc_connectorCollaredFibreMixtureZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
    FK.ocd_psiShift
        (rlc_connectorCollaredOuterDualGraph gamma gamma')
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (fun _ => False)
        (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi) p q *
      FK.activeBCZ (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerCollaredInducedWiring gamma gamma'
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
        (fun _ => p) q

theorem rlc_connectorCollaredFibreMixtureZ_eq_sum_outerWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorCollaredFibreMixtureZ gamma gamma' p q =
      ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
        ∑ eta : ConfigSpace
            (rlc_connectorInnerGraph gamma gamma').edgeSet,
          FK.bcWeight
            (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorCollaredOuterDualConfig gamma gamma'
              (rlc_connectorSplitSourceConfig
                gamma gamma' eta xi)) := by
  unfold rlc_connectorCollaredFibreMixtureZ FK.activeBCZ
  apply Finset.sum_congr rfl
  intro xi _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorCollaredSplitSource_outerWeight]
  ring

noncomputable def rlc_connectorCollaredFibreWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) : Real :=
  (FK.ocd_psiShift
        (rlc_connectorCollaredOuterDualGraph gamma gamma')
        (rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (fun _ => False)
        (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi) p q *
      FK.activeBCZ (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerCollaredInducedWiring gamma gamma'
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
        (fun _ => p) q) /
    rlc_connectorCollaredFibreMixtureZ gamma gamma' p q

theorem rlc_connectorCollaredFibreMixtureZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_connectorCollaredFibreMixtureZ gamma gamma' p q := by
  unfold rlc_connectorCollaredFibreMixtureZ
  apply Finset.sum_pos
  · intro xi _
    exact mul_pos
      (FK.ocd_psiShift_pos
        (Gout := rlc_connectorCollaredOuterDualGraph gamma gamma')
        (ιV := rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (bdryOut := fun _ => False) hp hp1 hq)
      (FK.activeBCZ_pos
        (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerCollaredInducedWiring gamma gamma'
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
        (fun _ => hp) (fun _ => hp1) hq)
  · exact Finset.univ_nonempty

theorem rlc_connectorCollaredFibreWeight_nonneg {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    0 ≤ rlc_connectorCollaredFibreWeight gamma gamma' p q xi := by
  unfold rlc_connectorCollaredFibreWeight
  exact div_nonneg
    (mul_nonneg
      (FK.ocd_psiShift_pos
        (Gout := rlc_connectorCollaredOuterDualGraph gamma gamma')
        (ιV := rlc_connectorInnerCollaredOuterVertex gamma gamma')
        (bdryOut := fun _ => False) hp hp1 hq).le
      (FK.activeBCZ_pos
        (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerCollaredInducedWiring gamma gamma'
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
        (fun _ => hp) (fun _ => hp1) hq).le)
    (rlc_connectorCollaredFibreMixtureZ_pos
      gamma gamma' hp hp1 hq).le

theorem rlc_connectorCollaredFibreWeight_sum_eq_one {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
      rlc_connectorCollaredFibreWeight gamma gamma' p q xi = 1 := by
  unfold rlc_connectorCollaredFibreWeight
    rlc_connectorCollaredFibreMixtureZ
  rw [← Finset.sum_div]
  exact div_self (rlc_connectorCollaredFibreMixtureZ_pos
    gamma gamma' hp hp1 hq).ne'

noncomputable def rlc_connectorCollaredSplitOuterEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) : Real :=
  (∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
      ∑ eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet,
        A.indicator (fun _ => (1 : Real)) eta *
          FK.bcWeight
            (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorCollaredOuterDualConfig gamma gamma'
              (rlc_connectorSplitSourceConfig
                gamma gamma' eta xi))) /
    rlc_connectorCollaredFibreMixtureZ gamma gamma' p q


theorem rlc_connectorCollaredSplitOuterEventMass_eq_fibreMixture {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorCollaredSplitOuterEventMass gamma gamma' p q A =
      ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
        rlc_connectorCollaredFibreWeight gamma gamma' p q xi *
          FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
            (rlc_connectorInnerCollaredInducedWiring gamma gamma'
              (rlc_connectorCollaredOuterStateOfSource
                gamma gamma' xi))
            (fun _ => p) q A := by
  unfold rlc_connectorCollaredSplitOuterEventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro xi _
  rw [show (∑ eta,
      A.indicator (fun _ => (1 : Real)) eta *
        FK.bcWeight
          (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q
          (rlc_connectorCollaredOuterDualConfig gamma gamma'
            (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) =
      FK.ocd_psiShift
          (rlc_connectorCollaredOuterDualGraph gamma gamma')
          (rlc_connectorInnerCollaredOuterVertex gamma gamma')
          (fun _ => False)
          (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)
          p q *
        FK.activeBCNumer (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerCollaredInducedWiring gamma gamma'
            (rlc_connectorCollaredOuterStateOfSource
              gamma gamma' xi))
          (fun _ => p) q (A.indicator fun _ => (1 : Real)) by
    unfold FK.activeBCNumer
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro eta _
    rw [rlc_connectorCollaredSplitSource_outerWeight]
    ring]
  unfold rlc_connectorCollaredFibreWeight FK.activeBCProbOf
  rw [FK.activeBCMean_eq_div]
  have hZi := (FK.activeBCZ_pos
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerCollaredInducedWiring gamma gamma'
      (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi))
    (fun _ => hp) (fun _ => hp1) hq).ne'
  field_simp

noncomputable def rlc_connectorCollaredOuterMaxConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma')) :=
  rlc_connectorCollaredOuterDualConfig gamma gamma' (fun _ => false)

theorem rlc_connectorCollaredOuterDualConfig_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorCollaredOuterDualConfig gamma gamma' tau ≤
      rlc_connectorCollaredOuterMaxConfig gamma gamma' := by
  intro a
  unfold rlc_connectorCollaredOuterMaxConfig
    rlc_connectorCollaredOuterDualConfig
  split
  · rename_i h
    unfold rlc_connectorForceTraceConfig
    split
    · rfl
    · cases tau h.choose.1 <;> simp
  · exact le_rfl

noncomputable def rlc_connectorInnerCollaredMaxInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorInnerVertex gamma gamma') :=
  rlc_connectorInnerCollaredInducedWiring gamma gamma'
    (rlc_connectorCollaredOuterMaxConfig gamma gamma')

noncomputable instance
    rlc_connectorInnerCollaredMaxInducedWiringDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_connectorInnerCollaredMaxInducedWiring gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_connectorInnerCollaredInducedWiring_mono {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {psi phi : ConfigSpace
      (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma'))}
    (hpsi : psi ≤ phi) :
    rlc_connectorInnerCollaredInducedWiring gamma gamma' psi ≤
      rlc_connectorInnerCollaredInducedWiring gamma gamma' phi := by
  intro x y hxy
  refine ⟨hxy.1, hxy.2.mono ?_⟩
  intro u v huv
  rw [FK.ocd_outsideGraph_adj] at huv ⊢
  rcases huv with hopen | hboundary
  · exact Or.inl ⟨hopen.1, hpsi _ hopen.2.1, hopen.2.2⟩
  · exact Or.inr hboundary

theorem rlc_connectorInnerCollaredInducedWiring_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorInnerCollaredInducedWiring gamma gamma'
        (rlc_connectorCollaredOuterDualConfig gamma gamma' tau) ≤
      rlc_connectorInnerCollaredMaxInducedWiring gamma gamma' := by
  exact rlc_connectorInnerCollaredInducedWiring_mono gamma gamma'
    (rlc_connectorCollaredOuterDualConfig_le_max gamma gamma' tau)



theorem rlc_connector_activeBCProbOf_q_one_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (pf : Sym2 V → Real) (A : Set (ConfigSpace G.edgeSet)) :
    FK.activeBCProbOf G C pf 1 A =
      FK.activeBCProbOf G D pf 1 A := by
  unfold FK.activeBCProbOf FK.activeBCMean FK.activeBCProb
    FK.activeBCZ FK.activeBCWeight
  simp only [one_pow, mul_one]



theorem rlc_connectorSplitOuterEventMass_q_one_eq_innerMerged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorSplitOuterEventMass gamma gamma' p 1 A =
      FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerMergedWiring gamma gamma')
        (fun _ => p) 1 A := by
  rw [rlc_connectorSplitOuterEventMass_eq_fibreMixture
    gamma gamma' hp hp1 zero_lt_one]
  simp_rw [rlc_connector_activeBCProbOf_q_one_independent
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerInducedWiring gamma gamma'
      (rlc_connectorOuterStateOfSource gamma gamma' _))
    (rlc_connectorInnerMergedWiring gamma gamma')]
  rw [← Finset.sum_mul,
    rlc_connectorFibreWeight_sum_eq_one
      gamma gamma' hp hp1 zero_lt_one, one_mul]



theorem rlc_connectorCollaredSplitOuterEventMass_q_one_eq_innerMerged
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorCollaredSplitOuterEventMass gamma gamma' p 1 A =
      FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerMergedWiring gamma gamma')
        (fun _ => p) 1 A := by
  rw [rlc_connectorCollaredSplitOuterEventMass_eq_fibreMixture
    gamma gamma' hp hp1 zero_lt_one]
  simp_rw [rlc_connector_activeBCProbOf_q_one_independent
    (rlc_connectorInnerGraph gamma gamma')
    (rlc_connectorInnerCollaredInducedWiring gamma gamma'
      (rlc_connectorCollaredOuterStateOfSource gamma gamma' _))
    (rlc_connectorInnerMergedWiring gamma gamma')]
  rw [← Finset.sum_mul,
    rlc_connectorCollaredFibreWeight_sum_eq_one
      gamma gamma' hp hp1 zero_lt_one, one_mul]



theorem rlc_connectorForcedDualReducedEventMass_q_one_eq_innerMerged
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) :
    rlc_connectorForcedDualEventMass gamma gamma' p 1
        (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A) =
      FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerMergedWiring gamma gamma')
        (fun _ => p) 1 A := by
  rw [rlc_connectorForcedDualReducedEventMass_eq_split
    gamma gamma' hp,
    rlc_connectorSplitOuterEventMass_q_one_eq_innerMerged
      gamma gamma' hp hp1]




noncomputable def rlc_connectorReflectedDualConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma' tau)
  fun e => decide (∃ f : Ising.kwg_Edge P,
    f.1 ∉ K.edgeSet ∧
      e.map Subtype.val =
        s(rlc_dualReflect (Ising.kwg_flankLeft P f),
          rlc_dualReflect (Ising.kwg_flankRight P f)))

@[simp] theorem rlc_connectorReflectedDualConfig_eq_true_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorReflectedDualConfig gamma gamma' tau e = true ↔
      ∃ f : Ising.kwg_Edge
          (rlc_connectorAugmentedPlanarDomain gamma gamma'),
        f.1 ∉ (FK.openSub
          (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet ∧
        e.map Subtype.val =
          s(rlc_dualReflect (Ising.kwg_flankLeft
              (rlc_connectorAugmentedPlanarDomain gamma gamma') f),
            rlc_dualReflect (Ising.kwg_flankRight
              (rlc_connectorAugmentedPlanarDomain gamma gamma') f)) := by
  simp [rlc_connectorReflectedDualConfig]





theorem rlc_connectorReflectedDualConfig_open_preimage_mem_connector
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (hopen : rlc_connectorReflectedDualConfig gamma gamma' tau e = true) :
    rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma' := by
  obtain ⟨⟨f, hfEdge⟩, hfClosed, he⟩ :=
    (rlc_connectorReflectedDualConfig_eq_true_iff
      gamma gamma' tau e).mp hopen
  induction f using Sym2.inductionOn with
  | _ x y =>
      have haug : (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp hfEdge
      change ((rlc_connectorFiniteGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y) at haug
      rcases haug with hfinite | htrace
      · have hpreimage : rlc_pimsEdgeEquiv (e.map Subtype.val) =
            s((x : RlcConnectorVertex n).val,
              (y : RlcConnectorVertex n).val) := by
          rw [he, rlc_pimsEdgeEquiv_reflected_mk_of_adj
            (Ising.kwg_flanks_adj _ ⟨s(x, y), hfEdge⟩),
            Ising.kwg_flanks_shared]
          rfl
        rw [hpreimage]
        exact hfinite.2
      · exfalso
        apply hfClosed
        apply (SimpleGraph.mem_edgeSet _).mpr
        rw [rlc_openSub_augmented_forceTrace]
        exact Or.inr htrace





theorem rlc_connectorReflectedDualConfig_le_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorReflectedDualConfig gamma gamma' tau <=
      rlc_connectorPIMSReflectedConfig gamma gamma' tau := by
  intro e
  by_cases hopen :
      rlc_connectorReflectedDualConfig gamma gamma' tau e = true
  · rw [hopen]
    obtain ⟨⟨f, hfEdge⟩, hfClosed, he⟩ :=
      (rlc_connectorReflectedDualConfig_eq_true_iff
        gamma gamma' tau e).mp hopen
    induction f using Sym2.inductionOn with
    | _ x y =>
        have haug :
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y :=
          (SimpleGraph.mem_edgeSet _).mp hfEdge
        change ((rlc_connectorFiniteGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y) at haug
        rcases haug with hfinite | htrace
        · have htau : tau s(x, y) = false :=
            Bool.eq_false_of_not_eq_true fun htau => hfClosed <|
              (SimpleGraph.mem_edgeSet _).mpr <| by
                rw [rlc_openSub_augmented_forceTrace]
                exact Or.inl ⟨hfinite, htau⟩
          have hpreimage :
              rlc_pimsEdgeEquiv (e.map Subtype.val) =
                s(x.val, y.val) := by
            rw [he, rlc_pimsEdgeEquiv_reflected_mk_of_adj
              (Ising.kwg_flanks_adj _
                ⟨s(x, y), hfEdge⟩), Ising.kwg_flanks_shared]
            rfl
          have hlift :
              rlc_connectorEdgeLift gamma gamma'
                  s(x.val, y.val) hfinite.2 = s(x, y) := by
            apply rlc_sym2Map_subtypeVal_injective
            rw [rlc_connectorEdgeLift_map]
            rfl
          have hliftClosed :
              tau (rlc_connectorEdgeLift gamma gamma'
                s(x.val, y.val) hfinite.2) = false := by
            rw [hlift]
            exact htau
          have hpims :
              rlc_connectorPIMSReflectedConfig gamma gamma' tau e = true := by
            rw [rlc_connectorPIMSReflectedConfig_apply, hpreimage,
              rlc_connectorAmbientMixedConfig_connectorEdge
                gamma gamma' tau hfinite.2, hliftClosed]
            rfl
          rw [hpims]
        · exfalso
          apply hfClosed
          apply (SimpleGraph.mem_edgeSet _).mpr
          rw [rlc_openSub_augmented_forceTrace]
          exact Or.inr htrace
  · have hclosed :
        rlc_connectorReflectedDualConfig gamma gamma' tau e = false :=
      Bool.eq_false_of_not_eq_true hopen
    rw [hclosed]
    exact Bool.false_le _




theorem rlc_connectorReflectedDualConfig_le_PIMSCollared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorReflectedDualConfig gamma gamma' tau <=
      rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau := by
  intro e
  by_cases hopen :
      rlc_connectorReflectedDualConfig gamma gamma' tau e = true
  · rw [hopen]
    obtain ⟨⟨f, hfEdge⟩, hfClosed, he⟩ :=
      (rlc_connectorReflectedDualConfig_eq_true_iff
        gamma gamma' tau e).mp hopen
    induction f using Sym2.inductionOn with
    | _ x y =>
        have haug :
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y :=
          (SimpleGraph.mem_edgeSet _).mp hfEdge
        change ((rlc_connectorFiniteGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y) at haug
        rcases haug with hfinite | htrace
        · have htau : tau s(x, y) = false :=
            Bool.eq_false_of_not_eq_true fun htau => hfClosed <|
              (SimpleGraph.mem_edgeSet _).mpr <| by
                rw [rlc_openSub_augmented_forceTrace]
                exact Or.inl ⟨hfinite, htau⟩
          have hpreimage :
              rlc_pimsEdgeEquiv (e.map Subtype.val) =
                s(x.val, y.val) := by
            rw [he, rlc_pimsEdgeEquiv_reflected_mk_of_adj
              (Ising.kwg_flanks_adj _
                ⟨s(x, y), hfEdge⟩), Ising.kwg_flanks_shared]
            rfl
          have hlift :
              rlc_connectorEdgeLift gamma gamma'
                  s(x.val, y.val) hfinite.2 = s(x, y) := by
            apply rlc_sym2Map_subtypeVal_injective
            rw [rlc_connectorEdgeLift_map]
            rfl
          have hliftClosed :
              tau (rlc_connectorEdgeLift gamma gamma'
                s(x.val, y.val) hfinite.2) = false := by
            rw [hlift]
            exact htau
          have hpims :
              rlc_connectorPIMSCollaredReflectedConfig
                  gamma gamma' tau e = true := by
            rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
              hpreimage,
              rlc_connectorAmbientCollaredConfig_connectorEdge
                gamma gamma' tau hfinite.2, hliftClosed]
            rfl
          rw [hpims]
        · exfalso
          apply hfClosed
          apply (SimpleGraph.mem_edgeSet _).mpr
          rw [rlc_openSub_augmented_forceTrace]
          exact Or.inr htrace
  · have hclosed :
        rlc_connectorReflectedDualConfig gamma gamma' tau e = false :=
      Bool.eq_false_of_not_eq_true hopen
    rw [hclosed]
    exact Bool.false_le _

theorem rlc_connectorForcedDualProb_nonneg {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    0 <= rlc_connectorForcedDualProb gamma gamma' p q tau := by
  unfold rlc_connectorForcedDualProb
  exact div_nonneg
    (BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)) hp hp1 hq).le
    (rlc_connectorForcedDualZ_pos gamma gamma' hp hp1 hq).le


theorem rlc_connectorForcedDualEventMass_mono {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {A B : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
    (hAB : A ⊆ B) :
    rlc_connectorForcedDualEventMass gamma gamma' p q A <=
      rlc_connectorForcedDualEventMass gamma gamma' p q B := by
  unfold rlc_connectorForcedDualEventMass
  apply Finset.sum_le_sum
  intro tau _
  by_cases htau : tau ∈ A
  · rw [Set.indicator_of_mem htau, Set.indicator_of_mem (hAB htau)]
  · rw [Set.indicator_of_notMem htau]
    have hind : 0 <= B.indicator (fun _ => (1 : Real)) tau :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) tau
    simpa using mul_nonneg hind
      (rlc_connectorForcedDualProb_nonneg gamma gamma' hp hp1 hq tau)



theorem rlc_bcEventMass_separate_eq_forcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A =
      rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.dualParam p q) q A := by
  unfold FK.bcEventMass rlc_connectorForcedDualEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_separate_eq_forcedDualProb gamma gamma' tau hp hp1 hq]



theorem rlc_bcProb_separate_selfDual_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {q : Real} (hq : 0 < q) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q tau =
      rlc_connectorForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q tau := by
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq
  simpa only [BeffaraDC.selfDualPoint_is_fixed hq] using
    rlc_bcProb_separate_eq_forcedDualProb gamma gamma' tau hp hp1 hq

theorem rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {q : Real} (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q A =
      rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q A := by
  unfold FK.bcEventMass rlc_connectorForcedDualEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_separate_selfDual_eq_forcedDualProb gamma gamma' tau hq]



theorem rlc_connectorComponentWiring_le_merged_of_oneAttachment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (hattach : RlcConnectorExteriorOneAttachment H) :
    rlc_connectorComponentWiring H ≤
      rlc_connectorMergedWiring gamma gamma' := by
  rw [rlc_connectorComponentWiring_eq_bot_of_oneAttachment H hattach]
  exact bot_le



theorem rlc_connectorPIMSCollaredInducedWiring_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorComponentWiring
        (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) ≤
      rlc_connectorMergedWiring gamma gamma' :=
  rlc_connectorComponentWiring_le_merged_of_oneAttachment
    gamma gamma' _
      (rlc_connectorPIMSCollaredExterior_oneAttachment gamma gamma' tau)



def rlc_connectorOnEither {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorVertex n) : Prop :=
  rlc_connectorOnRight gamma x ∨ rlc_connectorOnLeft gamma' x

noncomputable instance rlc_connectorOnEither_decidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (rlc_connectorOnEither gamma gamma') :=
  Classical.decPred _

def rlc_connectorMergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) :=
  Lattice.boundaryCliqueGraph (rlc_connectorOnEither gamma gamma')

noncomputable instance rlc_connectorMergedClique_decidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorMergedClique gamma gamma').Adj :=
  Classical.decRel _



theorem rlc_connectorMergedWiring_le_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorMergedWiring gamma gamma' ≤
      rlc_connectorMergedClique gamma gamma' := by
  intro x y hxy
  rw [rlc_connectorMergedClique, Lattice.boundaryCliqueGraph_adj]
  rcases hxy with hsep | hedge
  · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
    rcases hsep with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact ⟨hright.1, Or.inl hright.2.1, Or.inl hright.2.2⟩
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact ⟨hleft.1, Or.inr hleft.2.1, Or.inr hleft.2.2⟩
  · rw [SimpleGraph.edge_adj] at hedge
    rcases hedge with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hne⟩
    · exact ⟨hne, Or.inl (rlc_connectorRightAnchor_onRight gamma),
          Or.inr (rlc_connectorLeftAnchor_onLeft gamma')⟩
    · exact ⟨hne, Or.inr (rlc_connectorLeftAnchor_onLeft gamma'),
          Or.inl (rlc_connectorRightAnchor_onRight gamma)⟩



theorem rlc_connectorMergedWiring_reachable_onEither {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hx : rlc_connectorOnEither gamma gamma' x)
    (hy : rlc_connectorOnEither gamma gamma' y) :
    (rlc_connectorMergedWiring gamma gamma').Reachable x y := by
  have hanchor : (rlc_connectorMergedWiring gamma gamma').Reachable
      (rlc_connectorRightAnchor gamma)
      (rlc_connectorLeftAnchor gamma') := by
    by_cases h : rlc_connectorRightAnchor gamma =
        rlc_connectorLeftAnchor gamma'
    · rw [h]
    · exact (show (rlc_connectorMergedWiring gamma gamma').Adj
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') from Or.inr <|
            (SimpleGraph.edge_adj _ _ _ _).2
              ⟨Or.inl ⟨rfl, rfl⟩, h⟩).reachable
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (rlc_connectorTraceWiring_reachable_right gamma gamma' hx hy).mono
      ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
        le_sup_left)
  · exact ((rlc_connectorTraceWiring_reachable_right gamma gamma' hx
      (rlc_connectorRightAnchor_onRight gamma)).mono
        ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
          le_sup_left)).trans <|
      (hanchor.trans <|
        (rlc_connectorTraceWiring_reachable_left gamma gamma'
          (rlc_connectorLeftAnchor_onLeft gamma') hy).mono
            ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
              le_sup_left))
  · exact ((rlc_connectorTraceWiring_reachable_left gamma gamma' hx
      (rlc_connectorLeftAnchor_onLeft gamma')).mono
        ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
          le_sup_left)).trans <|
      (hanchor.symm.trans <|
        (rlc_connectorTraceWiring_reachable_right gamma gamma'
          (rlc_connectorRightAnchor_onRight gamma) hy).mono
            ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
              le_sup_left))
  · exact (rlc_connectorTraceWiring_reachable_left gamma gamma' hx hy).mono
      ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
        le_sup_left)



theorem rlc_connectorMergedWiring_reachable_iff_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (x y : RlcConnectorVertex n) :
    (H ⊔ rlc_connectorMergedWiring gamma gamma').Reachable x y ↔
      (H ⊔ rlc_connectorMergedClique gamma gamma').Reachable x y := by
  constructor
  · exact Reachable.mono (sup_le_sup_left
      (rlc_connectorMergedWiring_le_mergedClique gamma gamma') H)
  · intro hxy
    apply rlc_reachable_of_step_reachable
      (G := H ⊔ rlc_connectorMergedClique gamma gamma')
      (K := H ⊔ rlc_connectorMergedWiring gamma gamma') ?_ hxy
    intro u v huv
    rcases huv with hH | hclique
    · exact (show (H ⊔ rlc_connectorMergedWiring gamma gamma').Adj u v
        from Or.inl hH).reachable
    · rw [rlc_connectorMergedClique,
        Lattice.boundaryCliqueGraph_adj] at hclique
      exact (rlc_connectorMergedWiring_reachable_onEither
        gamma gamma' hclique.2.1 hclique.2.2).mono le_sup_right



theorem rlc_numClustersBC_mergedWiring_eq_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') tau =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedClique gamma gamma') tau := by
  unfold FK.numClustersBC
  apply Nat.card_congr
  let A := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
    rlc_connectorMergedWiring gamma gamma'
  let B := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
    rlc_connectorMergedClique gamma gamma'
  apply Equiv.ofBijective (fun C : A.ConnectedComponent =>
    B.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hB : B.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hA : A.Reachable C.out D.out :=
      (rlc_connectorMergedWiring_reachable_iff_mergedClique
        gamma gamma' _ C.out D.out).mpr hB
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hA
  · intro D
    let C := A.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hA : A.Reachable C.out D.out := ConnectedComponent.exact C.out_eq
    exact (rlc_connectorMergedWiring_reachable_iff_mergedClique
      gamma gamma' _ C.out D.out).mp hA



theorem rlc_bcProb_mergedWiring_eq_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') p q tau =
      FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedClique gamma gamma') p q tau := by
  unfold FK.bcProb FK.bcZ FK.bcWeight
  simp_rw [rlc_numClustersBC_mergedWiring_eq_mergedClique]

theorem rlc_bcEventMass_mergedWiring_eq_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') p q A =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedClique gamma gamma') p q A := by
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_mergedWiring_eq_mergedClique]



theorem rlc_connectorForcedDualEventMass_compl_le_merged_of_equiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    (D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ tau, tau ∉ A → D tau ∈ A)
    (hprob : ∀ tau,
      rlc_connectorForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q tau <=
        FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D tau)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q Aᶜ <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q A := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  unfold rlc_connectorForcedDualEventMass FK.bcEventMass
  rw [← Equiv.sum_comp D (fun eta :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
      A.indicator (fun _ => (1 : Real)) eta *
        FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta)]
  apply Finset.sum_le_sum
  intro tau _
  by_cases htau : tau ∈ A
  · rw [Set.indicator_of_notMem (by simpa using htau)]
    simp only [zero_mul]
    exact mul_nonneg (by
      by_cases hD : D tau ∈ A <;> simp [hD])
      (FK.bcProb_nonneg (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 (D tau))
  · rw [Set.indicator_of_mem (by simpa using htau),
      Set.indicator_of_mem (hfailure tau htau)]
    simpa using hprob tau


def rlc_finiteConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {tau | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau).Reachable x y}



theorem rlc_connectorEvent_iff_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_connectorEvent gamma gamma' ↔
      rlc_connectorRestrictConfig omega ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  rw [rlc_connectorEvent, rlc_finiteConnectorEvent]
  constructor
  · rintro ⟨x, hx, y, hy, hxR, hyR, hxy⟩
    refine ⟨⟨x, hxR⟩, ⟨y, hyR⟩, hx, hy, ?_⟩
    rw [rlc_openSub_connectorFiniteGraph_restrict_eq]
    exact hxy
  · rintro ⟨x, y, hx, hy, hxy⟩
    refine ⟨x, hx, y, hy, x.2, y.2, ?_⟩
    rw [rlc_openSub_connectorFiniteGraph_restrict_eq] at hxy
    exact hxy



theorem rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorAmbientMixedConfig gamma gamma' tau ∈
        rlc_connectorEvent gamma gamma' ↔
      tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
  rw [rlc_connectorEvent_iff_finite]
  unfold rlc_finiteConnectorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_restrict_ambientMixed_eq]




theorem rlc_finiteConnectorFailure_reflectedOpenDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma')
          (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      c.IsCycle := by
  apply rlc_connectorReachSet_reflectedOpenDualCircuit gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  intro hconn
  exact hno ((rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff
    gamma gamma' tau).mp hconn)



theorem rlc_connectorReachSet_openWalk_lift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u v : RlcConnectorVertex n}
    (hu : (u : Site 2) ∈ rlc_connectorReachSet gamma gamma' omega)
    (w : (openSubgraphInduce 2
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 * n) (2 * n) (-n) n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈ rlc_connectorReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_connectorReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2
          (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)).Adj
          (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈
          rlc_connectorReachSet gamma gamma' omega :=
        rlc_connectorReachSet_extend gamma gamma' omega hu b.2
          habOpen.1 habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habReach : ((hypercubicLattice 2).induce
          (rlc_connectorReachSet gamma gamma' omega)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := habOpen.1
      exact ⟨hc, habReach.reachable.trans hbc⟩



theorem rlc_connectorReachSet_rightPath_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1)
    (hy : y ∈ rlc_pathVertices gamma.1) :
    ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)).Reachable
        ⟨x, rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hx⟩
        ⟨y, rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hy⟩ := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hxW : x ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 x).2 hx
  have hyW : y ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 y).2 hy
  let wxy : (hypercubicLattice 2).Walk x y :=
    (W.takeUntil x hxW).reverse.append (W.takeUntil y hyW)
  have hwxy : ∀ z ∈ wxy.support,
      z ∈ rlc_connectorReachSet gamma gamma' omega := by
    intro z hz
    have hzW : z ∈ W.support := by
      dsimp only [wxy] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      rcases hz with hz | hz
      · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
      · exact W.support_takeUntil_subset_support hyW hz
    exact rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzW)
  exact ⟨wxy.induce (rlc_connectorReachSet gamma gamma' omega) hwxy⟩


theorem rlc_connectorReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hu0 := hu
  have hv0 := hv
  obtain ⟨huBox, xu, hxu, hxuBox, hxuReach⟩ := hu
  obtain ⟨hvBox, xv, hxv, hxvBox, hxvReach⟩ := hv
  have hxuFill := rlc_rightPathVertex_mem_connectorReachSet
    gamma gamma' omega hxu
  have hxvFill := rlc_rightPathVertex_mem_connectorReachSet
    gamma gamma' omega hxv
  obtain ⟨hu', hxuToU⟩ := rlc_connectorReachSet_openWalk_lift
    gamma gamma' omega hxuFill hxuReach.some
  obtain ⟨hv', hxvToV⟩ := rlc_connectorReachSet_openWalk_lift
    gamma gamma' omega hxvFill hxvReach.some
  have hsources := rlc_connectorReachSet_rightPath_reachable
    gamma gamma' omega hxu hxv
  have huEq : (⟨u, hu'⟩ : rlc_connectorReachSet gamma gamma' omega) =
      ⟨u, hu0⟩ := rfl
  have hvEq : (⟨v, hv'⟩ : rlc_connectorReachSet gamma gamma' omega) =
      ⟨v, hv0⟩ := rfl
  rw [huEq] at hxuToU
  rw [hvEq] at hxvToV
  exact hxuToU.symm.trans (hsources.trans hxvToV)



theorem rlc_connectorReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_connectorReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)) →g
      latticeMinusBarrier (rlc_connectorReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorReachSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h


noncomputable def rlc_connectorExteriorComponent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)ᶜ).ConnectedComponent :=
  Classical.choose (unique_infinite_component (by norm_num)
    (rlc_connectorReachSet gamma gamma' omega)
    (rlc_connectorReachSet_finite gamma gamma' omega))

theorem rlc_connectorExteriorComponent_infinite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_connectorExteriorComponent gamma gamma' omega).supp.Infinite :=
  (Classical.choose_spec (unique_infinite_component (by norm_num)
    (rlc_connectorReachSet gamma gamma' omega)
    (rlc_connectorReachSet_finite gamma gamma' omega))).1



def rlc_connectorExteriorSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) : Set (Site 2) :=
  {z | ∃ hz : z ∈ (rlc_connectorReachSet gamma gamma' omega)ᶜ,
    ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)ᶜ).connectedComponentMk
        ⟨z, hz⟩ = rlc_connectorExteriorComponent gamma gamma' omega}


def rlc_connectorFilledReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) : Set (Site 2) :=
  (rlc_connectorExteriorSet gamma gamma' omega)ᶜ

theorem rlc_connectorReachSet_subset_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_connectorReachSet gamma gamma' omega ⊆
      rlc_connectorFilledReachSet gamma gamma' omega := by
  intro z hz hExt
  obtain ⟨hzNot, _⟩ := hExt
  exact hzNot hz


theorem rlc_connectorExteriorSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorExteriorSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_connectorExteriorSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huNot, huComp⟩ := hu
  obtain ⟨hvNot, hvComp⟩ := hv
  have hcomp : ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)ᶜ).Reachable
      ⟨u, huNot⟩ ⟨v, hvNot⟩ :=
    ConnectedComponent.eq.mp (huComp.trans hvComp.symm)
  obtain ⟨w⟩ := hcomp
  let p : (hypercubicLattice 2).Walk u v :=
    w.map (SimpleGraph.Embedding.induce
      (rlc_connectorReachSet gamma gamma' omega)ᶜ).toHom
  have hpExt : ∀ z ∈ p.support,
      z ∈ rlc_connectorExteriorSet gamma gamma' omega := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce
        (rlc_connectorReachSet gamma gamma' omega)ᶜ).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    refine ⟨a.2, ?_⟩
    exact (ConnectedComponent.sound
      ⟨(w.takeUntil a ha).reverse⟩).trans huComp
  exact ⟨p.induce (rlc_connectorExteriorSet gamma gamma' omega) hpExt⟩




theorem rlc_connectorFilledReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_connectorFilledReachSet gamma gamma' omega).Finite := by
  let K := rlc_connectorReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorReachSet_finite gamma gamma' omega)
  apply (box_finite 2 R).subset
  intro z hzFill
  by_contra hzBox
  have hzExt : z ∈ exterior 2 R := by
    rw [exterior_eq_compl_box]
    exact hzBox
  have hzNotK : z ∈ Kᶜ := exterior_subset_compl K R hR hzExt
  have hzInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K R hR hzExt
  have hzComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩ = rlc_connectorExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorReachSet_finite gamma gamma' omega)).unique
        hzInf (rlc_connectorExteriorComponent_infinite gamma gamma' omega)
  exact hzFill ⟨hzNotK, hzComp⟩



theorem rlc_connectorExteriorSet_reachable_in_filledBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorExteriorSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorExteriorSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_connectorFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_not_mem _ hab
        (by
          simp only [rlc_connectorFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro a.2)
        (by
          simp only [rlc_connectorFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro b.2)
  }
  have h := (rlc_connectorExteriorSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h

private theorem rlc_walk_first_exit_set (A : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ (a b : Site 2) (p : (hypercubicLattice 2).Walk x a),
      (hypercubicLattice 2).Adj a b ∧
        (∀ z ∈ p.support, z ∈ A) ∧ b ∉ A := by
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ A
      · obtain ⟨u, v, q, huv, hq, hv⟩ := ih hb hy
        refine ⟨u, v, Walk.cons hab q, huv, ?_, hv⟩
        simp only [SimpleGraph.Walk.support_cons, List.forall_mem_cons]
        exact ⟨hx, hq⟩
      · exact ⟨a, b, Walk.nil, hab, by simpa, hb⟩



theorem rlc_connectorFilledReachSet_reaches_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u : Site 2}
    (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
    ∃ z : Site 2, ∃ hz : z ∈ rlc_connectorReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩
          ⟨z, rlc_connectorReachSet_subset_filled gamma gamma' omega hz⟩ := by
  let K := rlc_connectorReachSet gamma gamma' omega
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  by_cases huK : u ∈ K
  · exact ⟨u, huK, Reachable.refl _⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ Kᶜ,
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨u, huK⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huK, Reachable.refl _⟩
  let k : Site 2 := gamma.1.1
  have hkPath : k ∈ rlc_pathVertices gamma.1 :=
    rlc_path_start_mem_vertices gamma.1
  have hkK : k ∈ K :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hkPath
  have hkNotA : k ∉ A := by
    rintro ⟨hkNot, _⟩
    exact hkNot hkK
  obtain ⟨w⟩ := pbs_reach_all u k
  obtain ⟨a, b, q, hab, hqA, hbNotA⟩ :=
    rlc_walk_first_exit_set A w huA hkNotA
  have haA : a ∈ A := hqA a q.end_mem_support
  obtain ⟨haNotK, hua⟩ := haA
  have hbK : b ∈ K := by
    by_contra hbNotK
    have habK : ((hypercubicLattice 2).induce Kᶜ).Adj
        ⟨a, haNotK⟩ ⟨b, hbNotK⟩ := hab
    exact hbNotA ⟨hbNotK, hua.trans habK.reachable⟩
  have hAinH : A ⊆ H := by
    intro z hzA hzExt
    obtain ⟨hzNotK, huz⟩ := hzA
    obtain ⟨_hzNotK', hzComp⟩ := hzExt
    have huComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨u, huK⟩ = rlc_connectorExteriorComponent gamma gamma' omega :=
      (ConnectedComponent.sound huz).trans hzComp
    exact hu ⟨huK, huComp⟩
  have hqH : ∀ z ∈ q.support, z ∈ H := by
    intro z hz
    exact hAinH (hqA z hz)
  have huaH : ((hypercubicLattice 2).induce H).Reachable
      ⟨u, hu⟩ ⟨a, hAinH ⟨haNotK, hua⟩⟩ := ⟨q.induce H hqH⟩
  have hbH : b ∈ H := rlc_connectorReachSet_subset_filled
    gamma gamma' omega hbK
  have habH : ((hypercubicLattice 2).induce H).Adj
      ⟨a, hAinH ⟨haNotK, hua⟩⟩ ⟨b, hbH⟩ := hab
  exact ⟨b, hbK, huaH.trans habH.reachable⟩



theorem rlc_connectorFilledReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzu, huz⟩ :=
    rlc_connectorFilledReachSet_reaches_reachSet gamma gamma' omega hu
  obtain ⟨zv, hzv, hvz⟩ :=
    rlc_connectorFilledReachSet_reaches_reachSet gamma gamma' omega hv
  have hmiddle := (rlc_connectorReachSet_reachable
    gamma gamma' omega hzu hzv).map
      ((hypercubicLattice 2).induceHomOfLE
        (rlc_connectorReachSet_subset_filled gamma gamma' omega)).toHom
  exact huz.trans (hmiddle.trans hvz.symm)

theorem rlc_connectorFilledReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorFilledReachSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_connectorFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorFilledReachSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h



theorem rlc_connectorFilledReachSet_faceBoundaryConnected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    FaceBoundaryConnected (rlc_connectorFilledReachSet gamma gamma' omega)
      (phb_boundarySupport (rlc_connectorFilledReachSet gamma gamma' omega)
        (rlc_connectorFilledReachSet_finite gamma gamma' omega)) := by
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  let hH := rlc_connectorFilledReachSet_finite gamma gamma' omega
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_connectorReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_connectorReachSet_subset_filled gamma gamma' omega hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryConnected_of_connected_complement H hH hxH hyH
  · intro a b ha hb
    exact rlc_connectorFilledReachSet_reachable_in_barrier
      gamma gamma' omega ha hb
  · intro a b ha hb
    apply rlc_connectorExteriorSet_reachable_in_filledBarrier
      gamma gamma' omega
    · simpa [H, rlc_connectorFilledReachSet] using ha
    · simpa [H, rlc_connectorFilledReachSet] using hb





theorem rlc_connectorFilledBoundary_inside_mem_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {p q : Site 2}
    (hp : p ∈ rlc_connectorFilledReachSet gamma gamma' omega)
    (hq : q ∉ rlc_connectorFilledReachSet gamma gamma' omega)
    (hpq : (hypercubicLattice 2).Adj p q) :
    p ∈ rlc_connectorReachSet gamma gamma' omega := by
  let K := rlc_connectorReachSet gamma gamma' omega
  by_contra hpK
  have hqExt : q ∈ rlc_connectorExteriorSet gamma gamma' omega := by
    simpa [rlc_connectorFilledReachSet] using hq
  obtain ⟨hqK, hqComp⟩ := hqExt
  have hpqK : ((hypercubicLattice 2).induce Kᶜ).Adj
      ⟨p, hpK⟩ ⟨q, hqK⟩ := hpq
  have hpComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨p, hpK⟩ = rlc_connectorExteriorComponent gamma gamma' omega :=
    (ConnectedComponent.sound hpqK.reachable).trans hqComp
  exact hp ⟨hpK, hpComp⟩



theorem rlc_connectorFilled_edgeBoundary_subset_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {p q : Site 2}
    (hpq : (p, q) ∈ edgeBoundary 2
      (rlc_connectorFilledReachSet gamma gamma' omega)) :
    (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega) := by
  refine ⟨hpq.1, ?_⟩
  by_cases hp : p ∈ rlc_connectorFilledReachSet gamma gamma' omega
  · have hq : q ∉ rlc_connectorFilledReachSet gamma gamma' omega :=
      hpq.2.mp hp
    have hpK := rlc_connectorFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hp hq hpq.1
    have hqK : q ∉ rlc_connectorReachSet gamma gamma' omega := by
      intro hqK
      exact hq (rlc_connectorReachSet_subset_filled gamma gamma' omega hqK)
    exact iff_of_true hpK hqK
  · have hq : q ∈ rlc_connectorFilledReachSet gamma gamma' omega := by
      by_contra hq
      exact hp (hpq.2.mpr hq)
    have hqK := rlc_connectorFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hq hp hpq.1.symm
    have hpK : p ∉ rlc_connectorReachSet gamma gamma' omega := by
      intro hpK
      exact hp (rlc_connectorReachSet_subset_filled gamma gamma' omega hpK)
    simp [hpK, hqK]



theorem rlc_connectorFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma' omega) ≤
      faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega) := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqFilled : (p, q) ∈ edgeBoundary 2
      (rlc_connectorFilledReachSet gamma gamma' omega) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hpqReach := rlc_connectorFilled_edgeBoundary_subset_reachSet
    gamma gamma' omega hpqFilled
  rw [hpq, bdEdge_mk]
  exact hpqReach.2



theorem rlc_connectorFilledFaceBoundary_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_connectorFilledReachSet gamma gamma' omega)).support)
    (hg : g ∈ (faceBoundaryGraph
      (rlc_connectorFilledReachSet gamma gamma' omega)).support) :
    (faceBoundaryGraph
      (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable f g := by
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  let hH := rlc_connectorFilledReachSet_finite gamma gamma' omega
  have hconn := rlc_connectorFilledReachSet_faceBoundaryConnected
    gamma gamma' omega
  rw [FaceBoundaryConnected, SimpleGraph.connected_iff] at hconn
  have hfT : f ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hf
  have hgT : g ∈ phb_boundarySupport H hH := by
    simpa [H, hH] using hg
  have hreach := hconn.1 ⟨f, hfT⟩ ⟨g, hgT⟩
  exact hreach.map (SimpleGraph.Embedding.induce
    (phb_boundarySupport H hH : Set (Site 2))).toHom




theorem rlc_connector_faceBoundary_preimage_not_trace_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g) :
    sharedPrimalEdge f g ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  intro htrace
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma'
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  rcases Finset.mem_union.mp htrace with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 (hpq ▸ hright)
    have hpReach := rlc_rightPathVertex_mem_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau) hends.1
    have hqReach := rlc_rightPathVertex_mem_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau) hends.2
    exact (hpqBoundary.2.mp hpReach) hqReach
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 (hpq ▸ hleft)
    have hambNo : rlc_connectorAmbientMixedConfig gamma gamma' tau ∉
        rlc_connectorEvent gamma gamma' := by
      intro hconn
      exact hno ((rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff
        gamma gamma' tau).mp hconn)
    have hpNot := rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector
      gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      hambNo hends.1
    have hqNot := rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector
      gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      hambNo hends.2
    exact hpNot (hpqBoundary.2.mpr hqNot)



theorem rlc_connector_reflectedFaceBoundary_preimage_not_trace_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  rw [rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1]
  exact rlc_connector_faceBoundary_preimage_not_trace_of_failure
    gamma gamma' tau hno hfg



theorem rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    {x y : Site 2}
    (a : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk x y) :
    let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
      (rlc_connectorAmbientMixedConfig gamma gamma' tau)
    let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau)
    ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
      rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  dsimp only
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let p := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  intro e he
  have hEdges : p.edges = (a.mapLe hle).edges.map
      (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgEdge : s(f, g) ∈ a.edges := by
        rw [a.edges_mapLe_eq_edges hle] at he0
        exact he0
      change rlc_pimsEdgeEquiv
        s(rlc_dualReflect f, rlc_dualReflect g) ∉ _
      exact rlc_connector_reflectedFaceBoundary_preimage_not_trace_of_failure
        gamma gamma' tau hno (a.adj_of_mem_edges hfgEdge)


theorem rlc_connectorEdge_endpoint_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e) :
    z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
  rw [rlc_connectorEdges, Finset.mem_filter, mem_edgesWithinFinset] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he.1
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · simpa [rlc_connectorBox] using hx
  · simpa [rlc_connectorBox] using hy



theorem rlc_walk_support_mem_connectorBox_of_connectorEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {H : SimpleGraph (Site 2)} {x y : Site 2} (a : H.Walk x y)
    (hy : y ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
    (hedges : ∀ e ∈ a.edges,
      e ∈ rlc_connectorEdges gamma gamma') :
    ∀ z ∈ a.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hy
  · exact rlc_connectorEdge_endpoint_mem_box gamma gamma'
      (hedges e he) hze




def RlcConnectorPIMSBoundaryArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
        e ∈ rlc_connectorEdges gamma gamma'



def RlcConnectorPIMSFilledBoundaryContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y : Site 2,
    x ∈ (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).support ∧
    y ∈ (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).support ∧
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1



def RlcConnectorPIMSFilledBoundaryTargetSupported {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∀ {f g : Site 2},
    (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g →
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorEdges gamma gamma'



def rlc_traceSplitCounterexampleFiniteAllClosed :
    ConfigSpace (Sym2 (RlcConnectorVertex 1)) := fun _ => false







theorem rlc_traceSplitCounterexample_not_filledBoundaryTargetSupported :
    ¬ RlcConnectorPIMSFilledBoundaryTargetSupported
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      rlc_traceSplitCounterexampleFiniteAllClosed := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  let K := rlc_connectorReachSet gamma gamma' omega
  let H := rlc_connectorFilledReachSet gamma gamma' omega
  have hpPath : (![2, 0] : Site 2) ∈ rlc_pathVertices gamma.1 := by
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  have hpK : (![2, 0] : Site 2) ∈ K :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hpPath
  have hpH : (![2, 0] : Site 2) ∈ H :=
    rlc_connectorReachSet_subset_filled gamma gamma' omega hpK
  have hKbox : K ⊆ box 2 2 := by
    intro z hz
    have hzRect := rlc_connectorReachSet_subset_box gamma gamma' omega hz
    rw [mem_box]
    intro i
    fin_cases i <;> simp [mem_rect] at hzRect ⊢ <;> omega
  have hqExtBox : (![3, 0] : Site 2) ∈ exterior 2 2 := by
    rw [exterior_eq_compl_box, Set.mem_compl_iff, mem_box]
    simp
  have hqNotK : (![3, 0] : Site 2) ∈ Kᶜ :=
    exterior_subset_compl K 2 hKbox hqExtBox
  have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![3, 0], hqNotK⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K 2 hKbox hqExtBox
  have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![3, 0], hqNotK⟩ =
        rlc_connectorExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorReachSet_finite gamma gamma' omega)).unique hqInf
        (rlc_connectorExteriorComponent_infinite gamma gamma' omega)
  have hqExterior : (![3, 0] : Site 2) ∈
      rlc_connectorExteriorSet gamma gamma' omega := ⟨hqNotK, hqComp⟩
  have hqH : (![3, 0] : Site 2) ∉ H := by
    exact fun h => h hqExterior
  have hboundary : (faceBoundaryGraph H).Adj
      (![2, 0] : Site 2) ![2, -1] := by
    exact faceBoundaryGraph_adj_vert H 2 0 (iff_of_true hpH hqH)
  intro htarget
  have hedge : s((![-3, 1] : Site 2), ![-3, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    simpa [H, K, omega, tau, gamma, gamma', rlc_dualReflect,
      rlc_dualReflectFun] using htarget hboundary
  have hbox := rlc_connectorEdge_endpoint_mem_box gamma gamma' hedge
    (Sym2.mem_mk_left (![-3, 1] : Site 2) ![-3, 0])
  simp [mem_rect] at hbox



theorem rlc_traceSplitCounterexample_finiteAllClosed_reachSet_eq :
    rlc_connectorReachSet rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft
        (rlc_connectorAmbientMixedConfig rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_traceSplitCounterexampleFiniteAllClosed) =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  have hmask : rlc_maskConfig (rlc_connectorEdges gamma gamma') omega =
      (fun _ => false) := by
    funext e
    by_cases he : e ∈ rlc_connectorEdges gamma gamma'
    · simp [rlc_maskConfig, he, omega, tau,
        rlc_traceSplitCounterexampleFiniteAllClosed]
    · simp [rlc_maskConfig, he]
  apply Set.Subset.antisymm
  · rintro z ⟨hzBox, x, hxPath, hxBox, hxz⟩
    have hopen : openSubgraphInduce 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 : Int) 2 (-1) 1) = ⊥ := by
      ext u v
      simp [openSubgraphInduce_adj, hmask]
    have hxz' : ConnectedWithin 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 : Int) 2 (-1) 1)
        ⟨x, by simpa using hxBox⟩ ⟨z, by simpa using hzBox⟩ := by
      simpa [gamma, gamma', omega] using hxz
    change (openSubgraphInduce 2
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 : Int) 2 (-1) 1)).Reachable _ _ at hxz'
    rw [hopen] at hxz'
    have hxEq : x = z := congrArg Subtype.val
      (SimpleGraph.reachable_bot.mp hxz')
    simpa [gamma, hxEq] using hxPath
  · intro z hz
    exact rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega
      (by simpa [gamma] using hz)




theorem rlc_traceSplitCounterexample_finiteAllClosed_boundaryArc :
    RlcConnectorPIMSBoundaryArc rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_traceSplitCounterexampleFiniteAllClosed := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  let K := rlc_connectorReachSet gamma gamma' omega
  have hK : K =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) :=
    rlc_traceSplitCounterexample_finiteAllClosed_reachSet_eq
  have h01 : (faceBoundaryGraph K).Adj
      (![-1, -2] : Site 2) ![-1, -1] := by
    apply (faceBoundaryGraph_adj_vert K (-1) (-1) ?_).symm
    rw [hK, rlc_traceSplitCounterexample_right_vertices]
    simp
  have h12 : (faceBoundaryGraph K).Adj
      (![-1, -1] : Site 2) ![0, -1] := by
    apply (faceBoundaryGraph_adj_horiz K 0 (-1) ?_).symm
    rw [hK, rlc_traceSplitCounterexample_right_vertices]
    simp
  have h23 : (faceBoundaryGraph K).Adj
      (![0, -1] : Site 2) ![1, -1] := by
    apply (faceBoundaryGraph_adj_horiz K 1 (-1) ?_).symm
    rw [hK, rlc_traceSplitCounterexample_right_vertices]
    simp
  let a : (faceBoundaryGraph K).Walk
      (![-1, -2] : Site 2) ![1, -1] :=
    .cons h01 (.cons h12 (.cons h23 .nil))
  have hOrigin : (origin 2) ∈ rlc_connectorOriginRegion gamma gamma' := by
    rw [rlc_connectorOriginRegion]
    simp only [Set.Finite.mem_toFinset]
    have ho : origin 2 ∈ rlc_connectorAllowed gamma gamma' := by
      rw [rlc_connectorAllowed, Finset.mem_sdiff]
      constructor
      · simp [rlc_connectorBox, mem_rect, origin]
      · rw [show origin 2 = (![0, 0] : Site 2) by
          ext i
          fin_cases i <;> rfl]
        rw [rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices,
          rlc_traceSplitCounterexample_left_vertices]
        simp [rlc_flipX, rlc_flipXFun]
    exact ⟨ho, ho, Reachable.refl _⟩
  have hMinus : (![-1, 0] : Site 2) ∈
      rlc_connectorOriginRegion gamma gamma' := by
    have hOne : (![1, 0] : Site 2) ∈
        rlc_connectorOriginRegion gamma gamma' := by
      simpa [gamma, gamma'] using
        rlc_extremalSelection_one_zero_mem_originRegion
    have hflip := (rlc_connectorOriginRegion_mem_flipX_iff
      gamma gamma' (![1, 0] : Site 2)).mp hOne
    simpa [rlc_flipX, rlc_flipXFun] using hflip
  have he01 : s((![0, -1] : Site 2), ![0, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨![0, -1], by simp [rlc_connectorBox, mem_rect],
        ![0, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
    · refine ⟨origin 2, hOrigin, ?_⟩
      rw [show origin 2 = (![0, 0] : Site 2) by
        ext i
        fin_cases i <;> rfl]
      exact Sym2.mem_mk_right (![0, -1] : Site 2) ![0, 0]
  have he12 : s((![0, 0] : Site 2), ![-1, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨![0, 0], by simp [rlc_connectorBox, mem_rect],
        ![-1, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
    · exact ⟨![-1, 0], hMinus,
        Sym2.mem_mk_right (![0, 0] : Site 2) ![-1, 0]⟩
  have he23 : s((![-1, 0] : Site 2), ![-2, 0]) ∈
      rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨![-1, 0], by simp [rlc_connectorBox, mem_rect],
        ![-2, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
    · exact ⟨![-1, 0], hMinus,
        Sym2.mem_mk_left (![-1, 0] : Site 2) ![-2, 0]⟩
  refine ⟨![-1, -2], ![1, -1], a, ?_, ?_, ?_⟩
  · rw [rlc_traceSplitCounterexample_right_vertices]
    simp [rlc_dualReflect, rlc_dualReflectFun]
  · rw [rlc_traceSplitCounterexample_left_vertices]
    simp [rlc_dualReflect, rlc_dualReflectFun]
  · dsimp only
    let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma') omega
    let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' omega
    intro e he
    have hEdges : (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges =
        (a.mapLe hle).edges.map
          (Sym2.map (rlc_dualReflectOpenHom eta)) :=
      SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
    rw [hEdges] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    have heA : e0 ∈ a.edges := by
      rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at he0
    simp only [a, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil,
      or_false] at heA
    rcases heA with rfl | rfl | rfl
    · simpa [eta, rlc_dualReflectOpenHom, Sym2.map_mk,
        rlc_dualReflect, rlc_dualReflectFun] using he01
    · simpa [eta, rlc_dualReflectOpenHom, Sym2.map_mk,
        rlc_dualReflect, rlc_dualReflectFun] using he12
    · simpa [eta, rlc_dualReflectOpenHom, Sym2.map_mk,
        rlc_dualReflect, rlc_dualReflectFun] using he23



theorem rlc_traceSplitCounterexample_finiteAllClosed_failure :
    rlc_traceSplitCounterexampleFiniteAllClosed ∉
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  have hopen : FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau = ⊥ := by
    ext x y
    simp [FK.openSub_adj, tau,
      rlc_traceSplitCounterexampleFiniteAllClosed]
  have hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    rw [show gamma' = rlc_traceSplitCounterexampleLeft by rfl,
      rlc_traceSplitCounterexample_left_vertices] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  rintro ⟨x, y, hx, hy, hxy⟩
  rw [hopen] at hxy
  have hxyEq : x = y := SimpleGraph.reachable_bot.mp hxy
  subst y
  exact Finset.disjoint_left.mp hdisj hx hy




theorem rlc_traceSplitCounterexample_reflectedDual_failure :
    rlc_connectorReflectedDualConfig rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft
        rlc_traceSplitCounterexampleFiniteAllClosed ∉
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let tau := rlc_traceSplitCounterexampleFiniteAllClosed
  let rho := rlc_connectorReflectedDualConfig gamma gamma' tau
  have hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    rw [show gamma' = rlc_traceSplitCounterexampleLeft by rfl,
      rlc_traceSplitCounterexample_left_vertices] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  have hsourceNot {e : Sym2 (Site 2)}
      (hall : ∀ z ∈ e, z ∈ rlc_connectorBarrier gamma gamma') :
      e ∉ rlc_connectorEdges gamma gamma' := by
    intro he
    rw [rlc_connectorEdges, Finset.mem_filter] at he
    obtain ⟨z, hzRegion, hze⟩ := he.2
    exact rlc_originRegion_not_barrier hzRegion (hall z hze)
  have hrightIsolated (x y : RlcConnectorVertex 1)
      (hx : rlc_connectorOnRight gamma x)
      (hxy : (FK.openSub (rlc_connectorFiniteGraph gamma gamma') rho).Adj x y) :
      False := by
    rw [FK.openSub_adj] at hxy
    have hpre : rlc_pimsEdgeEquiv s((x : Site 2), (y : Site 2)) ∈
        rlc_connectorEdges gamma gamma' := by
      exact rlc_connectorReflectedDualConfig_open_preimage_mem_connector
        gamma gamma' tau s(x, y) (by simpa [rho, Sym2.map_mk] using hxy.2)
    have hxBarrier : (x : Site 2) ∈ rlc_connectorBarrier gamma gamma' := by
      simp only [rlc_connectorBarrier, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl hx))
    have htargetEdge := hxy.1.2
    rw [rlc_connectorEdges, Finset.mem_filter] at htargetEdge
    obtain ⟨z, hzRegion, hzEdge⟩ := htargetEdge.2
    have hyRegion : (y : Site 2) ∈
        rlc_connectorOriginRegion gamma gamma' := by
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with hz | hz
      · subst z
        exact False.elim (rlc_originRegion_not_barrier hzRegion hxBarrier)
      · simpa [hz] using hzRegion
    have hySet : (y : Site 2) ∈
        rlc_connectorOriginRegionSet gamma gamma' := by
      simpa [rlc_connectorOriginRegion] using hyRegion
    obtain ⟨hyAllowed, _ho, _hreach⟩ := hySet
    have hyBox : (y : Site 2) ∈ rlc_connectorBox 1 :=
      (Finset.mem_sdiff.mp hyAllowed).1
    have hyNotBarrier : (y : Site 2) ∉
        rlc_connectorBarrier gamma gamma' :=
      (Finset.mem_sdiff.mp hyAllowed).2
    have htarget :
        s((x : Site 2), (y : Site 2)) =
            s((![0, -1] : Site 2), ![0, 0]) ∨
          s((x : Site 2), (y : Site 2)) =
            s((![1, -1] : Site 2), ![1, 0]) ∨
          s((x : Site 2), (y : Site 2)) =
            s((![2, 0] : Site 2), ![1, 0]) := by
      change (x : Site 2) ∈ rlc_pathVertices gamma.1 at hx
      rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
        rlc_traceSplitCounterexample_right_vertices] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx | hx <;>
        (have hx0 := congrArg (fun z : Site 2 => z 0) hx
         have hx1 := congrArg (fun z : Site 2 => z 1) hx
         simp at hx0 hx1
         have hadj := hxy.1.1
         rw [hx] at hadj
         rcases adj_cases hadj with
          ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩ <;>
           simp at h0 h1)
      · have hyEq : (y : Site 2) = ![0, -2] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · left
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      · have hyEq : (y : Site 2) = ![-1, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp [rlc_flipX, rlc_flipXFun]
      · have hyEq : (y : Site 2) = ![1, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![1, -2] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · right; left
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      · have hyEq : (y : Site 2) = ![0, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![2, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![2, -2] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · have hyEq : (y : Site 2) = ![2, 0] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![1, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![3, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
      · have hyEq : (y : Site 2) = ![2, -1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp
      · have hyEq : (y : Site 2) = ![2, 1] := by
          ext i
          fin_cases i <;> simp <;> omega
        apply False.elim
        apply hyNotBarrier
        rw [hyEq, rlc_connectorBarrier,
          rlc_traceSplitCounterexample_left_vertices]
        simp [rlc_flipX, rlc_flipXFun]
      · right; right
        congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
      · have hyEq : (y : Site 2) = ![3, 0] := by
          ext i
          fin_cases i <;> simp <;> omega
        rw [hyEq, rlc_connectorBox] at hyBox
        simp [mem_rect] at hyBox
    rcases htarget with ht | ht | ht
    · have hs : s((![-1, -1] : Site 2), ![0, -1]) ∈
          rlc_connectorEdges gamma gamma' := by
        have hpims : rlc_pimsEdgeEquiv
            s((![0, -1] : Site 2), ![0, 0]) =
              s((![-1, -1] : Site 2), ![0, -1]) := by
          simpa using rlc_pimsEdgeEquiv_vertical 0 (-1)
        rw [ht, hpims] at hpre
        simpa using hpre
      exact hsourceNot (e := s((![-1, -1] : Site 2), ![0, -1])) (by
        intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;>
          rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_right_vertices] <;>
          simp [rlc_flipX, rlc_flipXFun]) hs
    · have hs : s((![-2, -1] : Site 2), ![-1, -1]) ∈
          rlc_connectorEdges gamma gamma' := by
        have hpims : rlc_pimsEdgeEquiv
            s((![1, -1] : Site 2), ![1, 0]) =
              s((![-2, -1] : Site 2), ![-1, -1]) := by
          simpa using rlc_pimsEdgeEquiv_vertical 1 (-1)
        rw [ht, hpims] at hpre
        simpa using hpre
      exact hsourceNot (e := s((![-2, -1] : Site 2), ![-1, -1])) (by
        intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl <;>
          rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_right_vertices] <;>
          simp [rlc_flipX, rlc_flipXFun]) hs
    · have hs : s((![-2, -1] : Site 2), ![-2, 0]) ∈
          rlc_connectorEdges gamma gamma' := by
        have hpims : rlc_pimsEdgeEquiv
            s((![1, 0] : Site 2), ![2, 0]) =
              s((![-2, -1] : Site 2), ![-2, 0]) := by
          simpa using rlc_pimsEdgeEquiv_horizontal 1 0
        rw [ht, show s((![2, 0] : Site 2), ![1, 0]) =
          s((![1, 0] : Site 2), ![2, 0]) from Sym2.eq_swap,
          hpims] at hpre
        simpa using hpre
      exact hsourceNot (e := s((![-2, -1] : Site 2), ![-2, 0])) (by
        intro z hz
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_right_vertices]
          simp [rlc_flipX, rlc_flipXFun]
        · rw [rlc_connectorBarrier,
            rlc_traceSplitCounterexample_left_vertices]
          simp) hs
  rintro ⟨x, y, hx, hy, hxy⟩
  obtain ⟨w⟩ := hxy
  cases w with
  | nil =>
      exact Finset.disjoint_left.mp hdisj hx hy
  | cons h _ => exact hrightIsolated x _ hx h





theorem rlc_connectorPIMSBoundaryArc_of_filledBoundary {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcontacts : RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau)
    (htarget : RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
    RlcConnectorPIMSBoundaryArc gamma gamma' tau := by
  obtain ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩ := hcontacts
  let omega := rlc_connectorAmbientMixedConfig gamma gamma' tau
  obtain ⟨p⟩ := rlc_connectorFilledFaceBoundary_reachable
    gamma gamma' omega hxSupp hySupp
  let hfill :=
    rlc_connectorFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
      gamma gamma' omega
  let a := p.mapLe hfill
  refine ⟨x, y, a, hxPath, hyPath, ?_⟩
  dsimp only
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma') omega
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' omega
  intro e he
  have hEdges : (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges =
      (a.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgA : s(f, g) ∈ a.edges := by
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he0
        exact he0
      have hfgP : s(f, g) ∈ p.edges := by
        dsimp only [a] at hfgA
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hfgA
        exact hfgA
      change s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorEdges gamma gamma'
      exact htarget (p.adj_of_mem_edges hfgP)



def RlcConnectorPIMSContourArcSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : Prop :=
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  (∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_orderedContourArc c hx hy).mapLe hle)).edges,
      e ∈ rlc_connectorEdges gamma gamma') ∨
    ∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_complementaryContourArc c hx hy).mapLe hle)).edges,
      e ∈ rlc_connectorEdges gamma gamma'



theorem rlc_connectorPIMSBoundaryArc_of_contourContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hside : RlcConnectorPIMSContourArcSide gamma gamma' tau c hx hy) :
    RlcConnectorPIMSBoundaryArc gamma gamma' tau := by
  rcases hside with hforward | hbackward
  · exact ⟨x, y, rlc_orderedContourArc c hx hy,
      hxPath, hyPath, hforward⟩
  · exact ⟨x, y, rlc_complementaryContourArc c hx hy,
      hxPath, hyPath, hbackward⟩


def RlcConnectorPIMSContourCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (u : Site 2)
    (c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk u u)
    (x y : Site 2) (hx : x ∈ c.support) (hy : y ∈ c.support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      RlcConnectorPIMSContourArcSide gamma gamma' tau c hx hy

theorem rlc_connectorPIMSBoundaryArc_of_contourCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (h : RlcConnectorPIMSContourCertificate gamma gamma' tau) :
    RlcConnectorPIMSBoundaryArc gamma gamma' tau := by
  obtain ⟨u, c, x, y, hx, hy, hxPath, hyPath, hside⟩ := h
  exact rlc_connectorPIMSBoundaryArc_of_contourContacts
    gamma gamma' tau c hx hy hxPath hyPath hside





def RlcConnectorPIMSSourceOpenCase {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2)) : Prop :=
  (∃ hsource : rlc_pimsEdgeEquiv e ∈ rlc_connectorEdges gamma gamma',
      tau (rlc_connectorEdgeLift gamma gamma'
        (rlc_pimsEdgeEquiv e) hsource) = false) ∨
    (rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma' ∧
      rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)


theorem rlc_connectorPIMSSourceOpenCase_not_trace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (hcase : RlcConnectorPIMSSourceOpenCase gamma gamma' tau e) :
    rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  rcases hcase with ⟨hsource, _⟩ | ⟨_, htrace⟩
  · intro he
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma')
          hright hsource
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma')
          hleft hsource
  · exact htrace




theorem rlc_connectorPIMSSourceOpenCase_of_maskedDual_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2))
    (hnotTrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hopen : rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)) e = true) :
    RlcConnectorPIMSSourceOpenCase gamma gamma' tau e := by
  rw [rlc_dualReflectConfig_eq_pims] at hopen
  by_cases hsource : rlc_pimsEdgeEquiv e ∈
      rlc_connectorEdges gamma gamma'
  · left
    refine ⟨hsource, ?_⟩
    simpa [rlc_maskConfig, hsource] using hopen
  · exact Or.inr ⟨hsource, hnotTrace⟩



theorem rlc_connectorPIMSReflectedConfig_open_of_sourceOpenCase {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2))
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (hcase : RlcConnectorPIMSSourceOpenCase gamma gamma' tau e) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau
      (rlc_connectorEdgeLift gamma gamma' e htarget) = true := by
  rw [rlc_connectorPIMSReflectedConfig_apply,
    rlc_connectorEdgeLift_map]
  rcases hcase with ⟨hsource, hclosed⟩ | ⟨hsource, htrace⟩
  · rw [rlc_connectorAmbientMixedConfig_connectorEdge
      gamma gamma' tau hsource, hclosed]
    rfl
  · simp [rlc_connectorAmbientMixedConfig, hsource, htrace]



def RlcConnectorPIMSActualSelectedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk x y),
    x ∈ rlc_pathVertices gamma.1 ∧
      y ∈ rlc_pathVertices gamma'.1 ∧
      (∀ z ∈ c.support,
        z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))) ∧
      (∀ e ∈ c.edges, e ∈ rlc_connectorEdges gamma gamma') ∧
      ∀ e ∈ c.edges,
        RlcConnectorPIMSSourceOpenCase gamma gamma' tau e




def RlcConnectorPIMSSupportedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk x y),
    x ∈ rlc_pathVertices gamma.1 ∧
      y ∈ rlc_pathVertices gamma'.1 ∧
      (∀ z ∈ c.support,
        z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))) ∧
      (∀ e ∈ c.edges, e ∈ rlc_connectorEdges gamma gamma') ∧
      ∀ e ∈ c.edges, rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1



theorem rlc_connectorPIMSSupportedArc_of_boundaryArc_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    (harc : RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    RlcConnectorPIMSSupportedArc gamma gamma' tau := by
  obtain ⟨x, y, a, hx, hy, htarget⟩ := harc
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let c := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  have hyBox : rlc_dualReflect y ∈
      (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) :=
    rlc_leftPathVertex_mem_connectorBox gamma' hy
  refine ⟨rlc_dualReflect x, rlc_dualReflect y, c, hx, hy, ?_, htarget, ?_⟩
  · exact rlc_walk_support_mem_connectorBox_of_connectorEdges
      gamma gamma' c hyBox htarget
  · exact rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure
      gamma gamma' tau hno a




theorem rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    (harc : RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    RlcConnectorPIMSActualSelectedArc gamma gamma' tau := by
  obtain ⟨x, y, a, hx, hy, htarget⟩ := harc
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let c := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  have hnotTrace : ∀ e ∈ c.edges, rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 :=
    rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure
      gamma gamma' tau hno a
  have hyBox : rlc_dualReflect y ∈
      (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) :=
    rlc_leftPathVertex_mem_connectorBox gamma' hy
  refine ⟨rlc_dualReflect x, rlc_dualReflect y, c, hx, hy, ?_,
    htarget, ?_⟩
  · exact rlc_walk_support_mem_connectorBox_of_connectorEdges
      gamma gamma' c hyBox htarget
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        exact rlc_connectorPIMSSourceOpenCase_of_maskedDual_open
          gamma gamma' tau s(u, v) (hnotTrace s(u, v) he)
            (c.adj_of_mem_edges he).2



theorem rlc_connectorPIMSSupportedArc_of_actualSelectedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcConnectorPIMSActualSelectedArc gamma gamma' tau) :
    RlcConnectorPIMSSupportedArc gamma gamma' tau := by
  obtain ⟨x, y, c, hx, hy, hsupp, htarget, hsource⟩ := harc
  exact ⟨x, y, c, hx, hy, hsupp, htarget, fun e he =>
    rlc_connectorPIMSSourceOpenCase_not_trace
      gamma gamma' tau (hsource e he)⟩



theorem rlc_connectorPIMS_openWalk_of_maskedDual_walk {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : Site 2}
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk x y)
    (hsupport : ∀ z ∈ c.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
    (htarget : ∀ e ∈ c.edges,
      e ∈ rlc_connectorEdges gamma gamma')
    (hnotTrace : ∀ e ∈ c.edges,
      rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    Nonempty ((FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSReflectedConfig gamma gamma' tau)).Walk
          ⟨x, hsupport x c.start_mem_support⟩
          ⟨y, hsupport y c.end_mem_support⟩) := by
  let cbox := c.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hsupport
  refine ⟨cbox.transfer
    (FK.openSub (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorPIMSReflectedConfig gamma gamma' tau)) ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      let hom := (SimpleGraph.Embedding.induce
        (G := openSubgraph 2 (rlc_dualReflectConfig
          (rlc_maskConfig (rlc_connectorEdges gamma gamma')
            (rlc_connectorAmbientMixedConfig gamma gamma' tau))))
        (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
      have hec : s((u : Site 2), (v : Site 2)) ∈ c.edges := by
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) cbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, by rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom cbox] at hmap
        simpa [hom, cbox] using hmap
      have hadj := c.adj_of_mem_edges hec
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      refine ⟨⟨hadj.1, htarget _ hec⟩, ?_⟩
      exact rlc_connectorPIMSReflectedConfig_open_of_masked_open
        gamma gamma' tau s(u, v)
        (by simpa [Sym2.map_mk] using hnotTrace _ hec)
        (by simpa [Sym2.map_mk] using hadj.2)



theorem rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcConnectorPIMSSupportedArc gamma gamma' tau) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' := by
  obtain ⟨x, y, c, hx, hy, hsupp, htarget, hnotTrace⟩ := harc
  obtain ⟨cfinite⟩ := rlc_connectorPIMS_openWalk_of_maskedDual_walk
    gamma gamma' tau c hsupp htarget hnotTrace
  exact ⟨⟨x, hsupp x c.start_mem_support⟩,
    ⟨y, hsupp y c.end_mem_support⟩, hx, hy, ⟨cfinite⟩⟩



theorem rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcConnectorPIMSActualSelectedArc gamma gamma' tau) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' := by
  exact rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc
    gamma gamma' tau
      (rlc_connectorPIMSSupportedArc_of_actualSelectedArc
        gamma gamma' tau harc)




theorem rlc_traceSplitCounterexample_PIMS_actualSelectedArc :
    RlcConnectorPIMSActualSelectedArc rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_traceSplitCounterexampleFiniteAllClosed := by
  exact rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure
    rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
    rlc_traceSplitCounterexampleFiniteAllClosed
    rlc_traceSplitCounterexample_finiteAllClosed_failure
    rlc_traceSplitCounterexample_finiteAllClosed_boundaryArc



theorem rlc_traceSplitCounterexample_PIMS_firstEdge_source_exterior :
    let e := s((![0, -1] : Site 2), ![0, 0])
    rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft ∧
      rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
          rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
  dsimp only
  have hpims : rlc_pimsEdgeEquiv
      s((![0, -1] : Site 2), ![0, 0]) =
        s((![-1, -1] : Site 2), ![0, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical 0 (-1)
  rw [hpims]
  constructor
  · intro he
    rw [rlc_connectorEdges, Finset.mem_filter] at he
    obtain ⟨z, hzRegion, hze⟩ := he.2
    apply rlc_originRegion_not_barrier hzRegion
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl <;>
      rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices] <;>
      simp [rlc_flipX, rlc_flipXFun]
  · intro he
    rcases Finset.mem_union.mp he with hright | hleft
    · have hends := rlc_pathEdge_endpoints_mem_vertices
        rlc_traceSplitCounterexampleRight.1 hright
      rw [rlc_traceSplitCounterexample_right_vertices] at hends
      simp at hends
    · have hends := rlc_pathEdge_endpoints_mem_vertices
        rlc_traceSplitCounterexampleLeft.1 hleft
      rw [rlc_traceSplitCounterexample_left_vertices] at hends
      simp at hends

theorem rlc_traceSplitCounterexample_PIMS_success_via_boundaryArc :
    rlc_connectorPIMSReflectedConfig rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft
        rlc_traceSplitCounterexampleFiniteAllClosed ∈
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  apply rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
    rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
    rlc_traceSplitCounterexampleFiniteAllClosed
  exact rlc_traceSplitCounterexample_PIMS_actualSelectedArc



theorem rlc_connectorPIMSReflectedConfig_mem_event_of_filledBoundary
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    (hcontacts : RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau)
    (htarget : RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' := by
  apply rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc
    gamma gamma' tau
  apply rlc_connectorPIMSSupportedArc_of_boundaryArc_of_failure
    gamma gamma' tau hno
  exact rlc_connectorPIMSBoundaryArc_of_filledBoundary
    gamma gamma' tau hcontacts htarget



theorem rlc_finiteConnectorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_finiteConnectorEvent gamma gamma') := by
  intro omega tau hot
  rintro ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  exact ⟨huv.1, hot _ huv.2⟩




def rlc_connectorPIMSVariableExteriorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {rho | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho ⊔
        rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y}



def rlc_connectorPIMSVariableWiredEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {rho | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho ⊔
        rlc_connectorPIMSExteriorWiring gamma gamma').Reachable x y}

theorem rlc_connectorPIMSVariableExteriorEvent_iff_wired {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rho ∈ rlc_connectorPIMSVariableWiredEvent gamma gamma' := by
  constructor <;> rintro ⟨x, y, hx, hy, hxy⟩
  · exact ⟨x, y, hx, hy,
      (rlc_connectorPIMSExterior_sup_reachable_iff_wiring
        gamma gamma' _ x y).mp hxy⟩
  · exact ⟨x, y, hx, hy,
      (rlc_connectorPIMSExterior_sup_reachable_iff_wiring
        gamma gamma' _ x y).mpr hxy⟩



theorem rlc_connectorPIMSVariableExteriorEvent_iff_assemble {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSAssembleConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  unfold rlc_connectorPIMSVariableExteriorEvent rlc_finiteConnectorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_PIMSAssembleConfig]



theorem rlc_PIMS_mem_finiteConnectorEvent_iff_variableExterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
        rlc_finiteConnectorEvent gamma gamma' ↔
      rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
        rlc_connectorPIMSVariableExteriorEvent gamma gamma' := by
  unfold rlc_finiteConnectorEvent rlc_connectorPIMSVariableExteriorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_PIMS_eq_variable_sup_exterior]



theorem rlc_connectorPIMSVariableExteriorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_connectorPIMSVariableExteriorEvent gamma gamma') := by
  intro rho sigma hrs
  rintro ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [SimpleGraph.sup_adj, FK.openSub_adj] at huv ⊢
  rcases huv with ⟨hvar, hopen⟩ | hext
  · exact Or.inl ⟨hvar, hrs _ hopen⟩
  · exact Or.inr hext

theorem rlc_connectorPIMSVariableWiredEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_connectorPIMSVariableWiredEvent gamma gamma') := by
  intro rho sigma hrs hrho
  rw [← rlc_connectorPIMSVariableExteriorEvent_iff_wired] at hrho ⊢
  exact rlc_connectorPIMSVariableExteriorEvent_isIncreasing
    gamma gamma' hrs hrho




theorem rlc_connectorPIMSReflectedConfig_mem_event_of_reflectedDual
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hdual : rlc_connectorReflectedDualConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma') :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' :=
  rlc_finiteConnectorEvent_isIncreasing gamma gamma'
    (rlc_connectorReflectedDualConfig_le_PIMS gamma gamma' tau) hdual



theorem rlc_connectorForcedDualEventMass_reflected_le_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_connectorForcedDualEventMass_mono gamma gamma' hp hp1 hq
  intro tau htau
  exact rlc_connectorPIMSReflectedConfig_mem_event_of_reflectedDual
    gamma gamma' tau htau



theorem rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hdual : rlc_connectorReflectedDualConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma') :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' :=
  rlc_finiteConnectorEvent_isIncreasing gamma gamma'
    (rlc_connectorReflectedDualConfig_le_PIMSCollared
      gamma gamma' tau) hdual


theorem rlc_connectorForcedDualEventMass_reflected_le_PIMSCollared
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_connectorForcedDualEventMass_mono gamma gamma' hp hp1 hq
  intro tau htau
  exact
    rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual
      gamma gamma' tau htau




theorem rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : C <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  exact FK.bcProb_mono_bc
    (rlc_connectorFiniteGraph gamma gamma') C
    (rlc_connectorMergedWiring gamma gamma') hC hp hp1 hq
    (rlc_finiteConnectorEvent_isIncreasing gamma gamma')




theorem rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma')) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  calc
    (∑ i, w i *
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) <=
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma') := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact FK.bcProb_mono_bc
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (rlc_connectorMergedWiring gamma gamma') (hC i) hp hp1 hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
    _ = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma') := by
      rw [← Finset.sum_mul, hwSum, one_mul]





theorem rlc_connectorPIMS_pushforward_le_merged_of_weightedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (pf : I → Sym2 (RlcConnectorVertex n) → Real)
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpf0 : ∀ i e, 0 <= pf i e)
    (hpf1 : ∀ i e, pf i e < 1)
    (hpfle : ∀ i e, pf i e <= BeffaraDC.selfDualPoint q)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (C i) (pf i) q omega)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  let target := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_finiteConnectorEvent gamma gamma')
  calc
    (∑ i, w i *
        (∑ omega,
          (rlc_finiteConnectorEvent gamma gamma').indicator
              (fun _ => (1 : Real)) omega *
            FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
              (C i) (pf i) q omega)) <=
        ∑ i, w i * target := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have hparam := FK.bcProbW_mono_params_of_nonneg
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (hpf0 i) (hpf1 i) (fun _ => hp.le) (fun _ => hp1)
        (hpfle i) hq (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      have hboundary := FK.bcProbW_mono_bc
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (rlc_connectorMergedWiring gamma gamma') (hC i)
        (fun _ => hp) (fun _ => hp1) hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      exact hparam.trans (by
        simpa only [FK.bcProbW_const, FK.bcEventMass, target]
          using hboundary)
    _ = target := by rw [← Finset.sum_mul, hwSum, one_mul]





theorem rlc_connectorPIMSCollared_pushforward_le_merged_of_weightedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (C i)
                (rlc_connectorPIMSCollaredParameter gamma gamma'
                  (BeffaraDC.selfDualPoint q)) q omega)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hpf0 : ∀ e, 0 <=
      rlc_connectorPIMSCollaredParameter gamma gamma'
        (BeffaraDC.selfDualPoint q) e := by
    intro e
    by_cases he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
        rlc_connectorEdges gamma gamma'
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_connector
        gamma gamma' _ e he]
      exact hp.le
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_exterior
        gamma gamma' _ e he]
  have hpf1 : ∀ e,
      rlc_connectorPIMSCollaredParameter gamma gamma'
          (BeffaraDC.selfDualPoint q) e < 1 := by
    intro e
    by_cases he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
        rlc_connectorEdges gamma gamma'
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_connector
        gamma gamma' _ e he]
      exact hp1
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_exterior
        gamma gamma' _ e he]
      exact zero_lt_one
  have hpfle : ∀ e,
      rlc_connectorPIMSCollaredParameter gamma gamma'
          (BeffaraDC.selfDualPoint q) e <=
        BeffaraDC.selfDualPoint q := by
    intro e
    by_cases he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
        rlc_connectorEdges gamma gamma'
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_connector
        gamma gamma' _ e he]
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_exterior
        gamma gamma' _ e he]
      exact hp.le
  rw [hpush]
  let target := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_finiteConnectorEvent gamma gamma')
  calc
    (∑ i, w i *
        (∑ omega,
          (rlc_finiteConnectorEvent gamma gamma').indicator
              (fun _ => (1 : Real)) omega *
            FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
              (C i)
              (rlc_connectorPIMSCollaredParameter gamma gamma'
                (BeffaraDC.selfDualPoint q)) q omega)) <=
        ∑ i, w i * target := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have hparam := FK.bcProbW_mono_params_of_nonneg
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        hpf0 hpf1 (fun _ => hp.le) (fun _ => hp1) hpfle hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      have hboundary := FK.bcProbW_mono_bc
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (rlc_connectorMergedWiring gamma gamma') (hC i)
        (fun _ => hp) (fun _ => hp1) hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      exact hparam.trans (by
        simpa only [FK.bcProbW_const, FK.bcEventMass, target]
          using hboundary)
    _ = target := by rw [← Finset.sum_mul, hwSum, one_mul]




theorem
    rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real)
    (tauExt : I → ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (rlc_connectorComponentWiring
                  (rlc_connectorPIMSCollaredExteriorOpenGraph
                    gamma gamma' (tauExt i)))
                (rlc_connectorPIMSCollaredParameter gamma gamma'
                  (BeffaraDC.selfDualPoint q)) q omega)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  exact
    rlc_connectorPIMSCollared_pushforward_le_merged_of_weightedMixture
      gamma gamma' hq w
      (fun i => rlc_connectorComponentWiring
        (rlc_connectorPIMSCollaredExteriorOpenGraph
          gamma gamma' (tauExt i)))
      hw hwSum
      (fun i => rlc_connectorPIMSCollaredInducedWiring_le_merged
        gamma gamma' (tauExt i)) hpush



theorem rlc_finiteConnectorEvent_iff_traceAnchors {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔
      (FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
        rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') := by
  let H := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hright := (rlc_connectorTraceWiring_reachable_right gamma gamma'
      (rlc_connectorRightAnchor_onRight gamma) hx).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    have hmiddle : (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y :=
      hxy.mono le_sup_left
    have hleft := (rlc_connectorTraceWiring_reachable_left gamma gamma'
      hy (rlc_connectorLeftAnchor_onLeft gamma')).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    exact hright.trans (hmiddle.trans hleft)
  · intro hanchors
    by_contra hno
    have hpropagate : ∀ {u v : RlcConnectorVertex n},
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Walk u v →
        (∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x u) →
        ∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x v := by
      intro u v w
      induction w with
      | nil => exact fun hu => hu
      | @cons u v z huv w ih =>
          intro hu
          apply ih
          rcases huv with hH | hsep
          · obtain ⟨x, hx, hxu⟩ := hu
            exact ⟨x, hx, hxu.trans hH.reachable⟩
          · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
            rcases hsep with hright | hleft
            · rw [Lattice.boundaryCliqueGraph_adj] at hright
              exact ⟨v, hright.2.2, Reachable.refl _⟩
            · rw [Lattice.boundaryCliqueGraph_adj] at hleft
              obtain ⟨x, hx, hxu⟩ := hu
              exact False.elim (hno ⟨x, u, hx, hleft.2.1, hxu⟩)
    have hanchorsSeparate :
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring gamma gamma' H
        (rlc_connectorRightAnchor gamma)
        (rlc_connectorLeftAnchor gamma')).mp hanchors
    obtain ⟨w⟩ := hanchorsSeparate
    obtain ⟨x, hx, hxleft⟩ := hpropagate w
      ⟨rlc_connectorRightAnchor gamma,
        rlc_connectorRightAnchor_onRight gamma, Reachable.refl _⟩
    exact hno ⟨x, rlc_connectorLeftAnchor gamma', hx,
      rlc_connectorLeftAnchor_onLeft gamma', hxleft⟩





theorem rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hext : rlc_connectorPIMSExteriorGraph gamma gamma' ≤
      rlc_connectorSeparateWiring gamma gamma') :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  let H := FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hxySeparate :
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable x y :=
      hxy.mono (sup_le_sup_left hext H)
    have hxyTrace :
        (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring
        gamma gamma' H x y).mpr hxySeparate
    have hright :
        (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma) x :=
      (rlc_connectorTraceWiring_reachable_right gamma gamma'
        (rlc_connectorRightAnchor_onRight gamma) hx).mono le_sup_right
    have hleft :
        (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable y
          (rlc_connectorLeftAnchor gamma') :=
      (rlc_connectorTraceWiring_reachable_left gamma gamma' hy
        (rlc_connectorLeftAnchor_onLeft gamma')).mono le_sup_right
    rw [rlc_finiteConnectorEvent_iff_traceAnchors,
      rlc_openSub_PIMSVariableConfig]
    exact hright.trans (hxyTrace.trans hleft)
  · intro hrho
    obtain ⟨x, y, hx, hy, hxy⟩ := hrho
    rw [rlc_openSub_PIMSVariableConfig] at hxy
    exact ⟨x, y, hx, hy, hxy.mono le_sup_left⟩



theorem rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_wiring_le
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hwire : rlc_connectorPIMSExteriorWiring gamma gamma' ≤
      rlc_connectorSeparateWiring gamma gamma') :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  apply rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le
  intro x y hxy
  exact hwire ⟨hxy.ne, hxy.reachable⟩



theorem rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_traceLocal
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma') :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' :=
  rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le
    gamma gamma' rho
      ((rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring
        gamma gamma').mp hlocal)




theorem rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_traceLocal
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma') :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
        rlc_finiteConnectorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma'
          (rlc_connectorPIMSReflectedConfig gamma gamma' tau) ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  rw [rlc_PIMS_mem_finiteConnectorEvent_iff_variableExterior]
  exact rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_traceLocal
    gamma gamma' _ hlocal




theorem rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_extremalSelection
    {n : Int}
    (hselection : RlcConnectorPIMSExtremalSelectionExteriorLocality n)
    (pair : RlcDiagonalPathPair n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hpair : omega ∈ rlc_extremalPairCandidate pair)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorPIMSReflectedConfig pair.1 pair.2 tau ∈
        rlc_finiteConnectorEvent pair.1 pair.2 ↔
      rlc_connectorPIMSVariableConfig pair.1 pair.2
          (rlc_connectorPIMSReflectedConfig pair.1 pair.2 tau) ∈
        rlc_finiteConnectorEvent pair.1 pair.2 :=
  rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_traceLocal
    pair.1 pair.2 tau (hselection pair ⟨omega, hpair⟩)



theorem rlc_finiteConnectorEvent_iff_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)).Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') := by
  rw [rlc_openSub_augmented_forceTrace]
  exact rlc_finiteConnectorEvent_iff_traceAnchors gamma gamma' tau





theorem rlc_finiteConnectorMass_ge_one_div_one_add_q {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hdual :
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') p q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply FrontierD.bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge
    (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma')
    hp hp1 hq (rlc_finiteConnectorEvent gamma gamma')
  simpa only [rlc_connectorMergedWiring] using hdual




theorem rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hdual :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteConnectorMass_ge_one_div_one_add_q
    gamma gamma' hp hp1 hq
  rw [rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass
    gamma gamma' (rlc_finiteConnectorEvent gamma gamma')ᶜ hq0]
  exact hdual




theorem rlc_finiteConnectorMass_selfDual_ge_of_reflected_equiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        D tau ∈ rlc_finiteConnectorEvent gamma gamma')
    (hprob : ∀ tau,
      rlc_connectorForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q tau <=
        FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D tau)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  exact rlc_connectorForcedDualEventMass_compl_le_merged_of_equiv
    gamma gamma' hq (rlc_finiteConnectorEvent gamma gamma')
      D hfailure hprob





theorem rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (F : ConfigSpace (Sym2 (RlcConnectorVertex n)) →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        F tau ∈ rlc_finiteConnectorEvent gamma gamma')
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (F ⁻¹' rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  apply (rlc_connectorForcedDualEventMass_mono gamma gamma'
    hp hp1 hq0 ?_).trans hdom
  intro tau htau
  exact hfailure tau (by simpa using htau)



theorem rlc_finiteConnectorMass_selfDual_ge_of_reflectedDual_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        rlc_connectorReflectedDualConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma')
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  exact rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination
    gamma gamma' hq (rlc_connectorReflectedDualConfig gamma gamma')
      hfailure hdom



theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma')
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  exact rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination
    gamma gamma' hq (rlc_connectorPIMSReflectedConfig gamma gamma')
      hfailure hdom




theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSArc_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSSupportedArc gamma gamma' tau)
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc
      gamma gamma' tau (harc tau hno)
  · exact hdom



theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSActualSelectedArc_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSActualSelectedArc gamma gamma' tau)
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
      gamma gamma' tau (harc tau hno)
  · exact hdom



theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSBoundaryArc gamma gamma' tau)
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSActualSelectedArc_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure
      gamma gamma' tau hno (harc tau hno)
  · exact hdom




theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedWiring
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : C <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma'))
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination
    gamma gamma' hq harc
  exact rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring
    gamma gamma' hq C hC hpush




theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma'))
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination
    gamma gamma' hq harc
  exact rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture
    gamma gamma' hq w C hw hwSum hC hpush





theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSFilledBoundary_inducedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma'))
    (hgeom : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau ∧
          RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSReflectedConfig_mem_event_of_filledBoundary
      gamma gamma' tau hno (hgeom tau hno).1 (hgeom tau hno).2
  · exact rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture
      gamma gamma' hq w C hw hwSum hC hpush





theorem
    rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollared_componentMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real)
    (tauExt : I → ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        rlc_connectorReflectedDualConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (rlc_connectorComponentWiring
                  (rlc_connectorPIMSCollaredExteriorOpenGraph
                    gamma gamma' (tauExt i)))
                (rlc_connectorPIMSCollaredParameter gamma gamma'
                  (BeffaraDC.selfDualPoint q)) q omega)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_reflectedDual_domination
    gamma gamma' hq hfailure
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  exact (rlc_connectorForcedDualEventMass_reflected_le_PIMSCollared
    gamma gamma' hp hp1 hq0).trans
      (rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture
        gamma gamma' hq w tauExt hw hwSum hpush)

end

end StatMech.Universality
