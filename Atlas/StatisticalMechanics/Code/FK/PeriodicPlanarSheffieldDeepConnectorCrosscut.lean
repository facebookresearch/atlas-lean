/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDeepConnectorCage





open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}




theorem PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_openWalk
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r R c d : Real} {width : Nat} {L U : Finset V}
    (hrR : r ≤ R)
    (h : omega ∈
      E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V,
      z ∉ E.rightHalfPlaneVertices r ∧
    ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V,
      w ∉ E.rightHalfPlaneVertices r ∧
    ∃ q : (P.openSubgraph omega).Walk z w,
      b ∈ q.support ∧ u ∈ q.support ∧
      ∀ v ∈ q.support, v = z ∨ v = w ∨
        v ∈ E.rightHalfPlaneVertices r := by
  rcases h.1.1 with
    ⟨x, hxL, hxInfinite, b, hb, _hbBoundary,
      z, hbz, hz, hbzOpen, hxb⟩
  rcases h.1.2 with
    ⟨y, hyU, hyInfinite, u, hu, _huBoundary,
      w, huw, hw, huwOpen, hyu⟩
  have hxy : omega ∈
      P.connectedWithinSet (E.rightHalfPlaneStripVertices R width) x y := by
    by_contra hnot
    apply h.2
    rw [PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion]
    apply Set.mem_iUnion.2
    refine ⟨⟨(x, y), Finset.mem_product.2 ⟨hxL, hyU⟩⟩, ?_⟩
    exact ⟨⟨hxInfinite, hyInfinite⟩, hnot⟩
  obtain ⟨qxb, hqxb⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk hxb
  obtain ⟨qyu, hqyu⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk hyu
  obtain ⟨qxy, hqxy⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk hxy
  have hbzAdj : (P.openSubgraph omega).Adj b z := ⟨hbz, hbzOpen⟩
  have huwAdj : (P.openSubgraph omega).Adj u w := ⟨huw, huwOpen⟩
  let left : (P.openSubgraph omega).Walk z x :=
    qxb.reverse.cons hbzAdj.symm
  let right : (P.openSubgraph omega).Walk y w :=
    qyu.append
      ((SimpleGraph.Walk.nil : (P.openSubgraph omega).Walk w w).cons huwAdj)
  let q : (P.openSubgraph omega).Walk z w :=
    (left.append qxy).append right
  refine ⟨b, hb, z, hz, u, hu, w, hw, q, ?_, ?_, ?_⟩
  · have hbLeft : b ∈ left.support := by
      dsimp only [left]
      rw [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_reverse]
      apply List.mem_cons_of_mem
      simpa using qxb.end_mem_support
    simp only [q, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl hbLeft)
  · have huRight : u ∈ right.support := by
      simp only [right, SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl qyu.end_mem_support
    simp only [q, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr huRight
  · intro v hv
    simp only [q, SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with (hv | hv) | hv
    · dsimp only [left] at hv
      rw [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_reverse] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hqxb v (by simpa using hv)))
    · exact Or.inr (Or.inr (hrR.trans
        (E.rightHalfPlaneStripVertices_subset R width (hqxy v hv))))
    · simp only [right, SimpleGraph.Walk.mem_support_append_iff] at hv
      rcases hv with hv | hv
      · exact Or.inr (Or.inr (hqyu v hv))
      · rw [SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil] at hv
        simp only [List.mem_cons] at hv
        rcases hv with hv | hv
        · exact Or.inr (Or.inr (hv.symm ▸ hu.1.1))
        · have hvw : v = w := by simpa using hv
          exact Or.inr (Or.inl hvw)



theorem PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_simpleCrosscut
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r R c d : Real} {width : Nat} {L U : Finset V}
    (hrR : r ≤ R) (hcd : c < d)
    (h : omega ∈
      E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ q : P.graph.Walk b u,
          q.IsPath ∧ ¬q.Nil ∧
          Function.Injective (E.simpleWalkArc q) ∧
          (∀ {x y : V}, s(x, y) ∈ q.edges →
            omega s(x, y) = true) ∧
          ∀ v ∈ q.support, v ∈ E.rightHalfPlaneVertices r := by
  obtain ⟨x, _hxL, _hxInfinite, b, hb, hxb,
    y, _hyU, _hyInfinite, u, hu, hyu, hxy⟩ :=
      E.finiteDeepOpenExitedJoinedBoundaryArmEvent_witnesses h
  obtain ⟨qxb, hqxb⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk hxb
  obtain ⟨qyu, hqyu⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk hyu
  obtain ⟨qxy, hqxy⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk hxy
  have hbu : b ≠ u := by
    intro hbu
    subst u
    have hbY := hb.2
    have huY := hu.2
    change E.vertexCoord b 1 ≤ c at hbY
    change d ≤ E.vertexCoord b 1 at huY
    linarith
  let joined : (P.openSubgraph omega).Walk b u :=
    (qxb.reverse.append qxy).append qyu
  let qOpen : (P.openSubgraph omega).Walk b u := joined.toPath
  have hopenLe : P.openSubgraph omega ≤ P.graph := by
    intro v w hvw
    exact ((P.openSubgraph_adj omega v w).mp hvw).1
  let q : P.graph.Walk b u := qOpen.mapLe hopenLe
  have hqEdgesOpen : qOpen.edges ⊆ joined.edges :=
    joined.edges_toPath_subset
  have hqSupportOpen : qOpen.support ⊆ joined.support :=
    joined.support_toPath_subset
  have hqNil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_ne hbu
  have hqOpenPath : qOpen.IsPath := by
    dsimp only [qOpen]
    exact joined.toPath.isPath
  have hqPath : q.IsPath := by
    exact hqOpenPath.mapLe hopenLe
  have hqEdges : q.edges = qOpen.edges := by
    exact SimpleGraph.Walk.edges_mapLe_eq_edges hopenLe qOpen
  have hqSupport : q.support = qOpen.support := by
    exact SimpleGraph.Walk.support_mapLe_eq_support hopenLe qOpen
  refine ⟨b, hb, u, hu, q, hqPath, hqNil,
    E.simpleWalkArc_injective_of_isPath q hqPath hqNil, ?_, ?_⟩
  · intro v w hvw
    rw [hqEdges] at hvw
    have hvwJoined := hqEdgesOpen hvw
    simp only [joined, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse] at hvwJoined
    rcases List.mem_append.mp hvwJoined with hvwLeft | hvwUpper
    · rcases List.mem_append.mp hvwLeft with hvwLower | hvwMiddle
      · exact ((P.openSubgraph_adj omega _ _).mp
          (qxb.adj_of_mem_edges (by simpa using hvwLower))).2
      · exact ((P.openSubgraph_adj omega _ _).mp
          (qxy.adj_of_mem_edges hvwMiddle)).2
    · exact ((P.openSubgraph_adj omega _ _).mp
        (qyu.adj_of_mem_edges hvwUpper)).2
  · intro v hv
    rw [hqSupport] at hv
    have hvJoined := hqSupportOpen hv
    simp only [joined, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hvJoined
    rcases hvJoined with (hvLower | hvMiddle) | hvUpper
    · exact hqxb v (by simpa using hvLower)
    · exact hrR.trans
        (E.rightHalfPlaneStripVertices_subset R width (hqxy v hvMiddle))
    · exact hqyu v hvUpper

end StatMech.FK.PeriodicPlanar
