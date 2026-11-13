/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffield










open Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



def PeriodicGraph.openSubgraphAmbientHom (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : P.openSubgraph omega →g P.graph :=
  SimpleGraph.Hom.ofLE fun _ _ h => h.1

@[simp] theorem PeriodicGraph.openSubgraphAmbientHom_apply
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (v : V) :
    P.openSubgraphAmbientHom omega v = v := rfl



def PeriodicPlaneEmbedding.openRectToOpenSubgraphHom
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (omega : ConfigSpace (Sym2 V)) :
    FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega) →g
      P.openSubgraph omega where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    rw [FK.openSub_adj] at hxy
    change P.graph.Adj x.1 y.1 ∧ omega s(x.1, y.1) = true
    exact ⟨SimpleGraph.induce_adj.mp hxy.1, hxy.2⟩

@[simp] theorem PeriodicPlaneEmbedding.openRectToOpenSubgraphHom_apply
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (omega : ConfigSpace (Sym2 V)) (v : E.RectVertex a b c d) :
    E.openRectToOpenSubgraphHom a b c d omega v = v.1 := rfl



theorem PeriodicPlaneEmbedding.map_openRectToOpenSubgraphHom_ambient
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (omega : ConfigSpace (Sym2 V))
    {x y : E.RectVertex a b c d}
    (p : (FK.openSub (E.rectGraph a b c d)
      (E.rectRestrict a b c d omega)).Walk x y) :
    (p.map (E.openRectToOpenSubgraphHom a b c d omega)).map
        (P.openSubgraphAmbientHom omega) =
      p.map (E.openRectHom a b c d (E.rectRestrict a b c d omega)) := by
  rw [SimpleGraph.Walk.map_map]
  congr 1



theorem PeriodicPlaneEmbedding.openSub_rectRestrict_eq_induce_gluing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (omega : ConfigSpace (Sym2 V)) :
    FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega) =
      (P.openSubgraph omega).induce (E.rectVertices a b c d) := by
  ext x y
  simp only [FK.openSub_adj, SimpleGraph.induce_adj,
    PeriodicGraph.openSubgraph_adj]
  rfl



theorem PeriodicPlaneEmbedding.exists_common_support_of_walkArc_intersection
    (E : PeriodicPlaneEmbedding P) {x y z w : V}
    (p : P.graph.Walk x y) (q : P.graph.Walk z w)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil) {r : ℂ}
    (hrp : r ∈ Set.range (E.walkArc p))
    (hrq : r ∈ Set.range (E.walkArc q)) :
    ∃ v : V, v ∈ p.support ∧ v ∈ q.support := by
  obtain ⟨a, b, hab, habp, hrab⟩ := E.mem_walkArc_range_of_not_nil p hp hrp
  obtain ⟨c, d, hcd, hcdq, hrcd⟩ := E.mem_walkArc_range_of_not_nil q hq hrq
  by_cases hedge : s(a, b) = s(c, d)
  · rw [Sym2.eq_iff] at hedge
    rcases hedge with hedge | hedge
    · refine ⟨a, p.fst_mem_support_of_mem_edges habp, ?_⟩
      simpa only [← hedge.1] using q.fst_mem_support_of_mem_edges hcdq
    · refine ⟨a, p.fst_mem_support_of_mem_edges habp, ?_⟩
      simpa only [← hedge.1] using q.snd_mem_support_of_mem_edges hcdq
  · obtain ⟨v, hvab, hvcd, _hvr⟩ :=
      E.edgeArc_intersection hab hcd r hedge hrab hrcd
    refine ⟨v, ?_, ?_⟩
    · rcases hvab with rfl | rfl
      · exact p.fst_mem_support_of_mem_edges habp
      · exact p.snd_mem_support_of_mem_edges habp
    · rcases hvcd with rfl | rfl
      · exact q.fst_mem_support_of_mem_edges hcdq
      · exact q.snd_mem_support_of_mem_edges hcdq



theorem PeriodicPlaneEmbedding.openWalk_start_reachable_of_walkArc_intersection
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    {x y z w : V} (p : (P.openSubgraph omega).Walk x y)
    (q : (P.openSubgraph omega).Walk z w) (hxy : x ≠ y) (hzw : z ≠ w)
    {r : ℂ}
    (hrp : r ∈ Set.range (E.walkArc (p.map (P.openSubgraphAmbientHom omega))))
    (hrq : r ∈ Set.range (E.walkArc (q.map (P.openSubgraphAmbientHom omega)))) :
    (P.openSubgraph omega).Reachable x z := by
  have hp : ¬ (p.map (P.openSubgraphAmbientHom omega)).Nil :=
    SimpleGraph.Walk.not_nil_of_ne hxy
  have hq : ¬ (q.map (P.openSubgraphAmbientHom omega)).Nil :=
    SimpleGraph.Walk.not_nil_of_ne hzw
  obtain ⟨v, hvp, hvq⟩ := E.exists_common_support_of_walkArc_intersection
    (p.map (P.openSubgraphAmbientHom omega))
    (q.map (P.openSubgraphAmbientHom omega)) hp hq hrp hrq
  have hvp' : v ∈ p.support := by
    rw [SimpleGraph.Walk.support_map] at hvp
    obtain ⟨u, hu, huv⟩ := List.mem_map.mp hvp
    change u = v at huv
    simpa only [huv] using hu
  have hvq' : v ∈ q.support := by
    rw [SimpleGraph.Walk.support_map] at hvq
    obtain ⟨u, hu, huv⟩ := List.mem_map.mp hvq
    change u = v at huv
    simpa only [huv] using hu
  exact (p.takeUntil v hvp').reachable.trans (q.takeUntil v hvq').reachable.symm




theorem PeriodicPlaneEmbedding.bufferedOpenRectWalks_start_reachable
    (E : PeriodicPlaneEmbedding P) {B a b c d av bv : ℝ}
    (hBpos : 0 < B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hav : a + 3 * B < av) (hbv : bv + 3 * B < b)
    (omega : ConfigSpace (Sym2 V))
    {xp yp : E.RectVertex a b (c + 4 * B) (d - 4 * B)}
    {xd yd : E.RectVertex av bv c d}
    (hxp : E.rectLeftBoundary a b (c + 4 * B) (d - 4 * B) xp)
    (hyp : E.rectRightBoundary a b (c + 4 * B) (d - 4 * B) yp)
    (hxd : E.rectBottomBoundary av bv c d xd)
    (hyd : E.rectTopBoundary av bv c d yd)
    (p : (FK.openSub (E.rectGraph a b (c + 4 * B) (d - 4 * B))
      (E.rectRestrict a b (c + 4 * B) (d - 4 * B) omega)).Walk xp yp)
    (q : (FK.openSub (E.rectGraph av bv c d)
      (E.rectRestrict av bv c d omega)).Walk xd yd) :
    ∃ r : (P.openSubgraph omega).Walk xp.1 xd.1,
      ∀ v ∈ r.support, v ∈ E.rectVertices a b c d := by
  obtain ⟨xl, hxl, hxlcoord⟩ := hxp
  obtain ⟨xr, hxr, hxrcoord⟩ := hyp
  obtain ⟨xb, hxb, hxbcoord⟩ := hxd
  obtain ⟨xt, hxt, hxtcoord⟩ := hyd
  let pfull : P.graph.Walk xp.1 yp.1 := p.map
    (E.openRectHom a b (c + 4 * B) (d - 4 * B)
      (E.rectRestrict a b (c + 4 * B) (d - 4 * B) omega))
  let qfull : P.graph.Walk xd.1 yd.1 := q.map
    (E.openRectHom av bv c d (E.rectRestrict av bv c d omega))
  let pOpen : (P.openSubgraph omega).Walk xp.1 yp.1 := p.map
    (E.openRectToOpenSubgraphHom a b (c + 4 * B) (d - 4 * B) omega)
  let qOpen : (P.openSubgraph omega).Walk xd.1 yd.1 := q.map
    (E.openRectToOpenSubgraphHom av bv c d omega)
  let gamma0 := E.walkArc pfull
  let eta0 := E.walkArc qfull
  let gamma := (E.edgeArc hxl).symm.trans (gamma0.trans (E.edgeArc hxr))
  let eta := (E.edgeArc hxb).symm.trans (eta0.trans (E.edgeArc hxt))
  have hxpNear := E.rectLeftBoundary_coord_lt hB
    (show E.rectLeftBoundary a b (c + 4 * B) (d - 4 * B) xp from
      ⟨xl, hxl, hxlcoord⟩)
  have hypNear := E.rectRightBoundary_coord_gt hB
    (show E.rectRightBoundary a b (c + 4 * B) (d - 4 * B) yp from
      ⟨xr, hxr, hxrcoord⟩)
  have hxdNear := E.rectBottomBoundary_coord_lt hB
    (show E.rectBottomBoundary av bv c d xd from ⟨xb, hxb, hxbcoord⟩)
  have hydNear := E.rectTopBoundary_coord_gt hB
    (show E.rectTopBoundary av bv c d yd from ⟨xt, hxt, hxtcoord⟩)
  have hxpyp : xp.1 ≠ yp.1 := by
    intro heq
    rw [heq] at hxpNear
    linarith
  have hxdyd : xd.1 ≠ yd.1 := by
    intro heq
    rw [heq] at hxdNear
    linarith
  have hgammaRect : Set.range gamma ⊆
      E.planeRect (a - B) (b + B)
        ((c + 4 * B) - B) ((d - 4 * B) + B) := by
    intro z hz
    dsimp only [gamma] at hz
    rw [Path.trans_range] at hz
    rcases hz with hleft | hrest
    · rw [Path.symm_range] at hleft
      obtain ⟨t, rfl⟩ := hleft
      exact E.edgeArc_mem_expanded_planeRect hB hxl xp.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact E.openRectWalkArc_range_subset hBpos.le hB p hcore
      · obtain ⟨t, rfl⟩ := hright
        exact E.edgeArc_mem_expanded_planeRect hB hxr yp.2 t
  have hetaRect : Set.range eta ⊆
      E.planeRect (av - B) (bv + B) (c - B) (d + B) := by
    intro z hz
    dsimp only [eta] at hz
    rw [Path.trans_range] at hz
    rcases hz with hbottom | hrest
    · rw [Path.symm_range] at hbottom
      obtain ⟨t, rfl⟩ := hbottom
      exact E.edgeArc_mem_expanded_planeRect hB hxb xd.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact E.openRectWalkArc_range_subset hBpos.le hB q hcore
      · obtain ⟨t, rfl⟩ := htop
        exact E.edgeArc_mem_expanded_planeRect hB hxt yd.2 t
  let gammaC := gamma.map E.coordinates.continuous
  let etaC := eta.map E.coordinates.continuous
  have hgammaY : ∀ t : unitInterval,
      c < gammaC t 1 ∧ gammaC t 1 < d := by
    intro t
    have ht := hgammaRect ⟨t, rfl⟩
    change c < E.coordinates (gamma t) 1 ∧ E.coordinates (gamma t) 1 < d
    change a - B ≤ E.coordinates (gamma t) 0 ∧
      E.coordinates (gamma t) 0 ≤ b + B ∧
      (c + 4 * B) - B ≤ E.coordinates (gamma t) 1 ∧
      E.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at ht
    constructor <;> linarith
  have hetaX : ∀ t : unitInterval,
      a < etaC t 0 ∧ etaC t 0 < b := by
    intro t
    have ht := hetaRect ⟨t, rfl⟩
    change a < E.coordinates (eta t) 0 ∧ E.coordinates (eta t) 0 < b
    change av - B ≤ E.coordinates (eta t) 0 ∧
      E.coordinates (eta t) 0 ≤ bv + B ∧
      c - B ≤ E.coordinates (eta t) 1 ∧
      E.coordinates (eta t) 1 ≤ d + B at ht
    constructor <;> linarith
  have hab0 : a < b := by linarith
  have hcd0 : c < d := by linarith
  obtain ⟨t, s, hcrossC⟩ :=
    ContinuousRectangleCrossing.strip_paths_intersect hab0 hcd0 gammaC etaC
      hxlcoord hxrcoord hxbcoord hxtcoord hgammaY hetaX
  have hcross : gamma t = eta s := by
    apply E.coordinates.injective
    simpa [gammaC, etaC] using hcrossC
  have htRect := hgammaRect ⟨t, rfl⟩
  have hsRect := hetaRect ⟨s, rfl⟩
  change a - B ≤ E.coordinates (gamma t) 0 ∧
    E.coordinates (gamma t) 0 ≤ b + B ∧
    (c + 4 * B) - B ≤ E.coordinates (gamma t) 1 ∧
    E.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at htRect
  change av - B ≤ E.coordinates (eta s) 0 ∧
    E.coordinates (eta s) 0 ≤ bv + B ∧
    c - B ≤ E.coordinates (eta s) 1 ∧
    E.coordinates (eta s) 1 ≤ d + B at hsRect
  have htCore : gamma t ∈ Set.range gamma0 := by
    have ht : gamma t ∈ Set.range gamma := ⟨t, rfl⟩
    dsimp only [gamma] at ht
    rw [Path.trans_range] at ht
    rcases ht with hleft | hrest
    · rw [Path.symm_range] at hleft
      obtain ⟨r, hr⟩ := hleft
      have hu := E.edgeArc_coord_le_vertex_add hB hxl r 0
      rw [hr, hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact hcore
      · obtain ⟨r, hr⟩ := hright
        have hu := E.vertex_sub_le_edgeArc_coord hB hxr r 0
        rw [hr, hcross] at hu
        linarith
  have hsCore : eta s ∈ Set.range eta0 := by
    have hs : eta s ∈ Set.range eta := ⟨s, rfl⟩
    dsimp only [eta] at hs
    rw [Path.trans_range] at hs
    rcases hs with hbottom | hrest
    · rw [Path.symm_range] at hbottom
      obtain ⟨r, hr⟩ := hbottom
      have hu := E.edgeArc_coord_le_vertex_add hB hxb r 1
      rw [hr, ← hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact hcore
      · obtain ⟨r, hr⟩ := htop
        have hu := E.vertex_sub_le_edgeArc_coord hB hxt r 1
        rw [hr, ← hcross] at hu
        linarith
  have hpfull : ¬ pfull.Nil := SimpleGraph.Walk.not_nil_of_ne hxpyp
  have hqfull : ¬ qfull.Nil := SimpleGraph.Walk.not_nil_of_ne hxdyd
  have hsCore' : gamma t ∈ Set.range eta0 := by
    rw [hcross]
    exact hsCore
  obtain ⟨v, hvpfull, hvqfull⟩ :=
    E.exists_common_support_of_walkArc_intersection
      pfull qfull hpfull hqfull htCore hsCore'
  have hvpOpen : v ∈ pOpen.support := by
    simpa [pOpen, pfull, SimpleGraph.Walk.support_map,
      PeriodicPlaneEmbedding.openRectHom,
      PeriodicPlaneEmbedding.openRectToOpenSubgraphHom] using hvpfull
  have hvqOpen : v ∈ qOpen.support := by
    simpa [qOpen, qfull, SimpleGraph.Walk.support_map,
      PeriodicPlaneEmbedding.openRectHom,
      PeriodicPlaneEmbedding.openRectToOpenSubgraphHom] using hvqfull
  let r : (P.openSubgraph omega).Walk xp.1 xd.1 :=
    (pOpen.takeUntil v hvpOpen).append (qOpen.takeUntil v hvqOpen).reverse
  refine ⟨r, ?_⟩
  intro w hw
  have hw' : w ∈ (pOpen.takeUntil v hvpOpen).support ∨
      w ∈ (qOpen.takeUntil v hvqOpen).reverse.support := by
    simpa only [r, SimpleGraph.Walk.mem_support_append_iff] using hw
  rcases hw' with hwp | hwq
  · have hwp' : w ∈ pOpen.support :=
      pOpen.support_takeUntil_subset_support hvpOpen hwp
    have hwpMap : w ∈ p.support.map Subtype.val := by
      simpa [pOpen, SimpleGraph.Walk.support_map,
        PeriodicPlaneEmbedding.openRectToOpenSubgraphHom] using hwp'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hwpMap
    exact ⟨u.2.1, u.2.2.1, by linarith [u.2.2.2.1],
      by linarith [u.2.2.2.2]⟩
  · have hwq' : w ∈ (qOpen.takeUntil v hvqOpen).support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hwq
    have hwq'' : w ∈ qOpen.support :=
      qOpen.support_takeUntil_subset_support hvqOpen hwq'
    have hwqMap : w ∈ q.support.map Subtype.val := by
      simpa [qOpen, SimpleGraph.Walk.support_map,
        PeriodicPlaneEmbedding.openRectToOpenSubgraphHom] using hwq''
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hwqMap
    exact ⟨by linarith [u.2.1], by linarith [u.2.2.1],
      u.2.2.2.1, u.2.2.2.2⟩



theorem PeriodicPlaneEmbedding.bufferedCrossings_openCluster
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hBpos : 0 < B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (omega : ConfigSpace (Sym2 V))
    (hH : omega ∈ E.horizontalCrossingEvent
      a b (c + 4 * B) (d - 4 * B))
    (hV : omega ∈ E.verticalCrossingEvent
      (a + 4 * B) (b - 4 * B) c d) :
    ∃ xp yp : E.RectVertex a b (c + 4 * B) (d - 4 * B),
      ∃ xd yd : E.RectVertex (a + 4 * B) (b - 4 * B) c d,
        E.rectLeftBoundary a b (c + 4 * B) (d - 4 * B) xp ∧
        E.rectRightBoundary a b (c + 4 * B) (d - 4 * B) yp ∧
        E.rectBottomBoundary (a + 4 * B) (b - 4 * B) c d xd ∧
        E.rectTopBoundary (a + 4 * B) (b - 4 * B) c d yd ∧
        (P.openSubgraph omega).Reachable xp.1 yp.1 ∧
        (P.openSubgraph omega).Reachable xd.1 yd.1 ∧
        (P.openSubgraph omega).Reachable xp.1 xd.1 := by
  change E.rectRestrict a b (c + 4 * B) (d - 4 * B) omega ∈
    E.finiteHorizontalCrossing a b (c + 4 * B) (d - 4 * B) at hH
  change E.rectRestrict (a + 4 * B) (b - 4 * B) c d omega ∈
    E.finiteVerticalCrossing (a + 4 * B) (b - 4 * B) c d at hV
  rcases hH with ⟨xp, yp, hxp, hyp, hpReach⟩
  rcases hV with ⟨xd, yd, hxd, hyd, hqReach⟩
  obtain ⟨p⟩ := hpReach
  obtain ⟨q⟩ := hqReach
  let pOpen : (P.openSubgraph omega).Walk xp.1 yp.1 := p.map
    (E.openRectToOpenSubgraphHom a b (c + 4 * B) (d - 4 * B) omega)
  let qOpen : (P.openSubgraph omega).Walk xd.1 yd.1 := q.map
    (E.openRectToOpenSubgraphHom (a + 4 * B) (b - 4 * B) c d omega)
  obtain ⟨r, _hr⟩ := E.bufferedOpenRectWalks_start_reachable hBpos hB hab hcd
    (by linarith) (by linarith) omega hxp hyp hxd hyd p q
  exact ⟨xp, yp, xd, yd, hxp, hyp, hxd, hyd,
    pOpen.reachable, qOpen.reachable, r.reachable⟩



theorem PeriodicPlaneEmbedding.overlapCrossings_glue_horizontal
    (E : PeriodicPlaneEmbedding P) {B a l m b c d : ℝ}
    (hBpos : 0 < B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hal : a ≤ l) (hmb : m ≤ b)
    (hleft : a + 5 * B < m - 5 * B)
    (hright : l + 5 * B < b - 5 * B)
    (hheight : c + 5 * B < d - 5 * B) :
    E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B) ∩
      (E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B) ∩
        E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d) ⊆
      E.horizontalCrossingEvent a b c d := by
  intro omega homega
  rcases homega with ⟨hHleft, hHright, hV⟩
  change E.rectRestrict a m (c + 4 * B) (d - 4 * B) omega ∈
    E.finiteHorizontalCrossing a m (c + 4 * B) (d - 4 * B) at hHleft
  change E.rectRestrict l b (c + 4 * B) (d - 4 * B) omega ∈
    E.finiteHorizontalCrossing l b (c + 4 * B) (d - 4 * B) at hHright
  change E.rectRestrict (l + 4 * B) (m - 4 * B) c d omega ∈
    E.finiteVerticalCrossing (l + 4 * B) (m - 4 * B) c d at hV
  rcases hHleft with ⟨xp, yp, hxp, hyp, hpReach⟩
  rcases hHright with ⟨xq, yq, hxq, hyq, hqReach⟩
  rcases hV with ⟨xv, yv, hxv, hyv, hvReach⟩
  obtain ⟨p⟩ := hpReach
  obtain ⟨q⟩ := hqReach
  obtain ⟨v⟩ := hvReach
  let qOpen : (P.openSubgraph omega).Walk xq.1 yq.1 := q.map
    (E.openRectToOpenSubgraphHom l b (c + 4 * B) (d - 4 * B) omega)
  obtain ⟨leftJoin, hleftJoin⟩ :=
    E.bufferedOpenRectWalks_start_reachable hBpos hB hleft hheight
      (by linarith) (by linarith) omega hxp hyp hxv hyv p v
  obtain ⟨rightJoin, hrightJoin⟩ :=
    E.bufferedOpenRectWalks_start_reachable hBpos hB hright hheight
      (by linarith) (by linarith) omega hxq hyq hxv hyv q v
  let joined : (P.openSubgraph omega).Walk xp.1 yq.1 :=
    (leftJoin.append rightJoin.reverse).append qOpen
  have hjSupport : ∀ w ∈ joined.support, w ∈ E.rectVertices a b c d := by
    intro w hw
    have hw' : w ∈ (leftJoin.append rightJoin.reverse).support ∨
        w ∈ qOpen.support := by
      simpa only [joined, SimpleGraph.Walk.mem_support_append_iff] using hw
    rcases hw' with hwpair | hwq
    · have hwpair' : w ∈ leftJoin.support ∨
          w ∈ rightJoin.reverse.support := by
        simpa only [SimpleGraph.Walk.mem_support_append_iff] using hwpair
      rcases hwpair' with hwl | hwr
      · have hwRect := hleftJoin w hwl
        exact ⟨hwRect.1, hwRect.2.1.trans hmb,
          hwRect.2.2.1, hwRect.2.2.2⟩
      · have hwr' : w ∈ rightJoin.support := by
          simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hwr
        have hwRect := hrightJoin w hwr'
        exact ⟨hal.trans hwRect.1, hwRect.2.1,
          hwRect.2.2.1, hwRect.2.2.2⟩
    · have hwq' : w ∈ q.support.map Subtype.val := by
        simpa [qOpen, SimpleGraph.Walk.support_map,
          PeriodicPlaneEmbedding.openRectToOpenSubgraphHom] using hwq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hwq'
      exact ⟨hal.trans u.2.1, u.2.2.1,
        by linarith [u.2.2.2.1], by linarith [u.2.2.2.2]⟩
  have hxpTarget : xp.1 ∈ E.rectVertices a b c d :=
    ⟨xp.2.1, xp.2.2.1.trans hmb,
      by linarith [xp.2.2.2.1], by linarith [xp.2.2.2.2]⟩
  have hyqTarget : yq.1 ∈ E.rectVertices a b c d :=
    ⟨hal.trans yq.2.1, yq.2.2.1,
      by linarith [yq.2.2.2.1], by linarith [yq.2.2.2.2]⟩
  let xpTarget : E.RectVertex a b c d := ⟨xp.1, hxpTarget⟩
  let yqTarget : E.RectVertex a b c d := ⟨yq.1, hyqTarget⟩
  have hleftTarget : E.rectLeftBoundary a b c d xpTarget := by
    obtain ⟨z, hxz, hz⟩ := hxp
    exact ⟨z, hxz, hz⟩
  have hrightTarget : E.rectRightBoundary a b c d yqTarget := by
    obtain ⟨z, hyz, hz⟩ := hyq
    exact ⟨z, hyz, hz⟩
  change E.rectRestrict a b c d omega ∈ E.finiteHorizontalCrossing a b c d
  refine ⟨xpTarget, yqTarget, hleftTarget, hrightTarget, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce_gluing]
  exact ⟨joined.induce (E.rectVertices a b c d) hjSupport⟩

end StatMech.FK.PeriodicPlanar
