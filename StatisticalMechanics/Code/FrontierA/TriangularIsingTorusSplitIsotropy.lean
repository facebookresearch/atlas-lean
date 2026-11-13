/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSplitHomology
import Code.FrontierA.TriangularIsingTorusFacePotential
import Code.FrontierA.SurfaceKacWardQuadraticAssembly
import Code.Onsager.TorusIntersection











namespace StatMech.FrontierA

open SimpleGraph StatMech.Ising StatMech.Onsager

theorem triangularTorusSplitEmbedVertex_fst_mod_three
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    (triangularTorusSplitEmbedVertex L p).1.val % 3 =
      (triangularTorusSplitOffset
        (triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) p))).1 := by
  rw [triangularTorusSplitEmbedVertex_fst_val]
  simp [Nat.add_mod,
    Nat.mod_eq_of_lt (triangularTorusSplitOffset_fst_lt_three _)]

theorem triangularTorusSplitEmbedVertex_snd_mod_three
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    (triangularTorusSplitEmbedVertex L p).2.val % 3 =
      (triangularTorusSplitOffset
        (triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) p))).2 := by
  rw [triangularTorusSplitEmbedVertex_snd_val]
  simp [Nat.add_mod,
    Nat.mod_eq_of_lt (triangularTorusSplitOffset_snd_lt_three _)]

theorem triangular_zmod_val_add_one_mod_three
    (L : Nat) [Fact (2 < L)] (z : ZMod (3 * L)) :
    (z + 1).val % 3 = (z.val + 1) % 3 := by
  letI : Fact (1 < 3 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  rw [ZMod.val_add, ZMod.val_one,
    Nat.mod_mod_of_dvd _ ⟨L, rfl⟩]

theorem triangular_nat_add_one_mod_three (n : Nat) :
    (n + 1) % 3 = (n % 3 + 1) % 3 := by
  simpa using Nat.add_mod n 1 3

theorem triangularTorusNortheastEdge_eq_pair
    (N : Nat) [Fact (2 < N)] (z : ZMod N × ZMod N) :
    triangularTorusNortheastEdge N z =
      s(z, (z.1 + 1, z.2 + 1)) := by
  rcases z with ⟨x, y⟩
  simp [triangularTorusNortheastEdge,
    triangularTorusDartEquiv_apply, triangularTorusDartToGraphDart,
    triangularTorusDirectionStep, SimpleGraph.Dart.edge]

theorem triangularTorusSplitOffset_no_diagonalCorner :
    ∀ a b c : Fin 6,
      (triangularTorusSplitOffset b).1 =
          ((triangularTorusSplitOffset a).1 + 1) % 3 →
      (triangularTorusSplitOffset b).2 =
          ((triangularTorusSplitOffset a).2 + 1) % 3 →
      (triangularTorusSplitOffset c).1 =
          ((triangularTorusSplitOffset a).1 + 1) % 3 →
      (triangularTorusSplitOffset c).2 =
          (triangularTorusSplitOffset a).2 → False := by
  decide



theorem triangularTorusSplitEmbed_diagonalCorner_not_mem_range
    (L : Nat) [Fact (2 < L)]
    (p q r : KWDartPort (triangularTorusGraph L))
    (z : ZMod (3 * L) × ZMod (3 * L))
    (hedge : s(triangularTorusSplitEmbedVertex L p,
        triangularTorusSplitEmbedVertex L q) =
      triangularTorusNortheastEdge (3 * L) z) :
    triangularTorusSplitEmbedVertex L r ≠ (z.1 + 1, z.2) := by
  rw [triangularTorusNortheastEdge_eq_pair] at hedge
  rw [Sym2.eq_iff] at hedge
  rintro hr
  have hpX := triangularTorusSplitEmbedVertex_fst_mod_three L p
  have hpY := triangularTorusSplitEmbedVertex_snd_mod_three L p
  have hqX := triangularTorusSplitEmbedVertex_fst_mod_three L q
  have hqY := triangularTorusSplitEmbedVertex_snd_mod_three L q
  have hrX := triangularTorusSplitEmbedVertex_fst_mod_three L r
  have hrY := triangularTorusSplitEmbedVertex_snd_mod_three L r
  generalize hpa : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) p) = a at hpX hpY
  generalize hqa : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) q) = b at hqX hqY
  generalize hra : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) r) = c at hrX hrY
  rcases hedge with h | h
  · have hpq : triangularTorusSplitEmbedVertex L q =
        ((triangularTorusSplitEmbedVertex L p).1 + 1,
          (triangularTorusSplitEmbedVertex L p).2 + 1) := by
      rw [h.1]
      exact h.2
    have hpr : triangularTorusSplitEmbedVertex L r =
        ((triangularTorusSplitEmbedVertex L p).1 + 1,
          (triangularTorusSplitEmbedVertex L p).2) := by
      rw [h.1]
      exact hr
    have hqx := congrArg (fun w => w.1) hpq
    have hqy := congrArg (fun w => w.2) hpq
    have hrx := congrArg (fun w => w.1) hpr
    have hry := congrArg (fun w => w.2) hpr
    have hqx' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hqx
    have hqy' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hqy
    have hrx' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hrx
    have hry' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hry
    simp only [triangular_zmod_val_add_one_mod_three] at hqx' hqy' hrx'
    apply triangularTorusSplitOffset_no_diagonalCorner a b c
    · exact hqX.symm.trans <| hqx'.trans <|
        (triangular_nat_add_one_mod_three _).trans <|
          congrArg (fun n : Nat => (n + 1) % 3) hpX
    · exact hqY.symm.trans <| hqy'.trans <|
        (triangular_nat_add_one_mod_three _).trans <|
          congrArg (fun n : Nat => (n + 1) % 3) hpY
    · exact hrX.symm.trans <| hrx'.trans <|
        (triangular_nat_add_one_mod_three _).trans <|
          congrArg (fun n : Nat => (n + 1) % 3) hpX
    · exact hrY.symm.trans <| hry'.trans hpY
  · have hqp : triangularTorusSplitEmbedVertex L p =
        ((triangularTorusSplitEmbedVertex L q).1 + 1,
          (triangularTorusSplitEmbedVertex L q).2 + 1) := by
      rw [h.2]
      exact h.1
    have hqr : triangularTorusSplitEmbedVertex L r =
        ((triangularTorusSplitEmbedVertex L q).1 + 1,
          (triangularTorusSplitEmbedVertex L q).2) := by
      rw [h.2]
      exact hr
    have hpx := congrArg (fun w => w.1) hqp
    have hpy := congrArg (fun w => w.2) hqp
    have hrx := congrArg (fun w => w.1) hqr
    have hry := congrArg (fun w => w.2) hqr
    have hpx' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hpx
    have hpy' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hpy
    have hrx' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hrx
    have hry' := congrArg (fun w : ZMod (3 * L) => w.val % 3) hry
    simp only [triangular_zmod_val_add_one_mod_three] at hpx' hpy' hrx'
    apply triangularTorusSplitOffset_no_diagonalCorner b a c
    · exact hpX.symm.trans <| hpx'.trans <|
        (triangular_nat_add_one_mod_three _).trans <|
          congrArg (fun n : Nat => (n + 1) % 3) hqX
    · exact hpY.symm.trans <| hpy'.trans <|
        (triangular_nat_add_one_mod_three _).trans <|
          congrArg (fun n : Nat => (n + 1) % 3) hqY
    · exact hrX.symm.trans <| hrx'.trans <|
        (triangular_nat_add_one_mod_three _).trans <|
          congrArg (fun n : Nat => (n + 1) % 3) hqX
    · exact hrY.symm.trans <| hry'.trans hqY




theorem triangularSquareExpansion_vertex_carrier
    (N : Nat) [Fact (2 < N)]
    (F : Finset (Sym2 (ZMod N × ZMod N)))
    (edge : Sym2 (ZMod N × ZMod N))
    (hedge : edge ∈ triangularSquareExpansion N F)
    (z : ZMod N × ZMod N) (hz : z ∈ edge) :
    (∃ original ∈ F, z ∈ original) ∨
      ∃ p, triangularTorusNortheastEdge N p ∈ F ∧
        z = (p.1 + 1, p.2) := by
  rw [triangularSquareExpansion, Finset.mem_union] at hedge
  rcases hedge with hedge | hedge
  · rw [triangularSquareHorizontalEdges, Finset.mem_symmDiff] at hedge
    rcases hedge with ⟨heast, -⟩ | ⟨hdiag, -⟩
    · rw [Finset.mem_image] at heast
      obtain ⟨p, hp, rfl⟩ := heast
      left
      refine ⟨triangularTorusEastEdge N p, (Finset.mem_filter.mp hp).2, ?_⟩
      rwa [triangularTorusEastEdge_eq_ons]
    · rw [Finset.mem_image] at hdiag
      obtain ⟨p, hp, rfl⟩ := hdiag
      have hpF := (Finset.mem_filter.mp hp).2
      rw [ons_portEdge, ons_dirStep, Sym2.mem_iff] at hz
      rcases hz with hz | hz
      · left
        refine ⟨triangularTorusNortheastEdge N p, hpF, ?_⟩
        rw [triangularTorusNortheastEdge_eq_pair, Sym2.mem_iff]
        exact Or.inl hz
      · right
        exact ⟨p, hpF, hz⟩
  · rw [triangularSquareVerticalEdges, Finset.mem_symmDiff] at hedge
    rcases hedge with ⟨hnorth, -⟩ | ⟨hdiag, -⟩
    · rw [Finset.mem_image] at hnorth
      obtain ⟨p, hp, rfl⟩ := hnorth
      left
      refine ⟨triangularTorusNorthEdge N p, (Finset.mem_filter.mp hp).2, ?_⟩
      rwa [triangularTorusNorthEdge_eq_ons]
    · rw [Finset.mem_image] at hdiag
      obtain ⟨p, hp, rfl⟩ := hdiag
      have hpF := (Finset.mem_filter.mp hp).2
      rw [ons_portEdge, ons_dirStep, Sym2.mem_iff] at hz
      rcases hz with hz | hz
      · right
        exact ⟨p, hpF, hz⟩
      · left
        refine ⟨triangularTorusNortheastEdge N p, hpF, ?_⟩
        rw [triangularTorusNortheastEdge_eq_pair, Sym2.mem_iff]
        exact Or.inr hz



theorem triangularTorusSplitEmbedWalk_diagonalCorner_not_mem_support
    (L : Nat) [Fact (2 < L)]
    {u v x y : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v)
    (q : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk x y)
    (z : ZMod (3 * L) × ZMod (3 * L))
    (hdiag : triangularTorusNortheastEdge (3 * L) z ∈
      (triangularTorusSplitEmbedWalk L p).edges.toFinset) :
    (z.1 + 1, z.2) ∉ (triangularTorusSplitEmbedWalk L q).support := by
  rw [List.mem_toFinset, triangularTorusSplitEmbedWalk_edges,
    List.mem_map] at hdiag
  obtain ⟨edge, hedge, hmap⟩ := hdiag
  rw [SimpleGraph.Walk.edges, List.mem_map] at hedge
  obtain ⟨d, hd, rfl⟩ := hedge
  have hrealized :
      s(triangularTorusSplitEmbedVertex L d.fst,
        triangularTorusSplitEmbedVertex L d.snd) =
          triangularTorusNortheastEdge (3 * L) z := by
    simpa [SimpleGraph.Dart.edge, Sym2.map_pair_eq] using hmap
  intro hcorner
  rw [triangularTorusSplitEmbedWalk_support, List.mem_map] at hcorner
  obtain ⟨r, hr, hre⟩ := hcorner
  exact triangularTorusSplitEmbed_diagonalCorner_not_mem_range
    L d.fst d.snd r z hrealized hre



theorem triangularTorusSplitEmbedWalk_squareExpansion_incCount_disjoint
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u u)
    (q : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk v v)
    (hdisjoint : Disjoint
      (triangularTorusSplitEmbedWalk L p).toSubgraph.verts
      (triangularTorusSplitEmbedWalk L q).toSubgraph.verts) :
    ∀ z, incCount
        (triangularSquareExpansion (3 * L)
          (triangularTorusSplitEmbedWalk L p).edges.toFinset) z = 0 ∨
      incCount
        (triangularSquareExpansion (3 * L)
          (triangularTorusSplitEmbedWalk L q).edges.toFinset) z = 0 := by
  intro z
  by_cases hpzero : incCount
      (triangularSquareExpansion (3 * L)
        (triangularTorusSplitEmbedWalk L p).edges.toFinset) z = 0
  · exact Or.inl hpzero
  right
  by_contra hqzero
  have hpedge : ∃ edge ∈ triangularSquareExpansion (3 * L)
      (triangularTorusSplitEmbedWalk L p).edges.toFinset, z ∈ edge := by
    unfold incCount at hpzero
    obtain ⟨edge, hedge⟩ := Finset.card_ne_zero.mp hpzero
    exact ⟨edge, (Finset.mem_filter.mp hedge).1,
      (Finset.mem_filter.mp hedge).2⟩
  have hqedge : ∃ edge ∈ triangularSquareExpansion (3 * L)
      (triangularTorusSplitEmbedWalk L q).edges.toFinset, z ∈ edge := by
    unfold incCount at hqzero
    obtain ⟨edge, hedge⟩ := Finset.card_ne_zero.mp hqzero
    exact ⟨edge, (Finset.mem_filter.mp hedge).1,
      (Finset.mem_filter.mp hedge).2⟩
  obtain ⟨pedge, hpedge, hzpedge⟩ := hpedge
  obtain ⟨qedge, hqedge, hzqedge⟩ := hqedge
  have hpCarrier := triangularSquareExpansion_vertex_carrier
    (3 * L) (triangularTorusSplitEmbedWalk L p).edges.toFinset
      pedge hpedge z hzpedge
  have hqCarrier := triangularSquareExpansion_vertex_carrier
    (3 * L) (triangularTorusSplitEmbedWalk L q).edges.toFinset
      qedge hqedge z hzqedge
  have hcontra (w : ZMod (3 * L) × ZMod (3 * L))
      (hpz : w ∈ (triangularTorusSplitEmbedWalk L p).support)
      (hqz : w ∈ (triangularTorusSplitEmbedWalk L q).support) : False :=
    Set.disjoint_left.1 hdisjoint
      ((SimpleGraph.Walk.mem_verts_toSubgraph _).mpr hpz)
      ((SimpleGraph.Walk.mem_verts_toSubgraph _).mpr hqz)
  rcases hpCarrier with hpOriginal | ⟨a, ha, hza⟩
  · obtain ⟨edge, hedge, hzedge⟩ := hpOriginal
    have hpz : z ∈ (triangularTorusSplitEmbedWalk L p).support :=
      SimpleGraph.Walk.mem_support_of_mem_edges
        (List.mem_toFinset.mp hedge) hzedge
    rcases hqCarrier with hqOriginal | ⟨b, hb, hzb⟩
    · obtain ⟨edge, hedge, hzedge⟩ := hqOriginal
      exact hcontra z hpz <|
        SimpleGraph.Walk.mem_support_of_mem_edges
          (List.mem_toFinset.mp hedge) hzedge
    · apply triangularTorusSplitEmbedWalk_diagonalCorner_not_mem_support
        L q p b hb
      rwa [hzb] at hpz
  · rcases hqCarrier with hqOriginal | ⟨b, hb, hzb⟩
    · obtain ⟨edge, hedge, hzedge⟩ := hqOriginal
      have hqz : z ∈ (triangularTorusSplitEmbedWalk L q).support :=
        SimpleGraph.Walk.mem_support_of_mem_edges
          (List.mem_toFinset.mp hedge) hzedge
      apply triangularTorusSplitEmbedWalk_diagonalCorner_not_mem_support
        L p q a ha
      rwa [hza] at hqz
    · have hab : a = b := by
        have hc : (a.1 + 1, a.2) = (b.1 + 1, b.2) :=
          hza.symm.trans hzb
        have hx : a.1 + 1 = b.1 + 1 := congrArg Prod.fst hc
        have hy0 := congrArg
          (fun w : ZMod (3 * L) × ZMod (3 * L) => w.2) hc
        have hy : a.2 = b.2 := by simpa using hy0
        exact Prod.ext (add_right_cancel hx) hy
      subst b
      have haz : a ∈ triangularTorusNortheastEdge (3 * L) a := by
        rw [triangularTorusNortheastEdge_eq_pair, Sym2.mem_iff]
        exact Or.inl rfl
      exact hcontra a
        (SimpleGraph.Walk.mem_support_of_mem_edges
          (List.mem_toFinset.mp ha) haz)
        (SimpleGraph.Walk.mem_support_of_mem_edges
          (List.mem_toFinset.mp hb) haz)

theorem surfaceIntersection_genus_one_eq_ons
    (h k : Fin 2 × Fin 2) :
    surfaceIntersection
        (fun _ : Fin 1 => h.1, fun _ : Fin 1 => h.2)
        (fun _ : Fin 1 => k.1, fun _ : Fin 1 => k.2) =
      ons_homologyIntersection h k := by
  simp [surfaceIntersection, ons_homologyIntersection, Fin.sum_univ_one]



theorem triangularTorus_localAngularSplit_disjointCycleIsotropic
    (L : Nat) [Fact (2 < L)] :
    SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L))
      (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) := by
  intro u v p q hp hq hdisjoint
  let P := triangularTorusSplitEmbedWalk L p
  let Q := triangularTorusSplitEmbedWalk L q
  have hPcycle : P.IsCycle :=
    triangularTorusSplitEmbedWalk_isCycle L p hp
  have hQcycle : Q.IsCycle :=
    triangularTorusSplitEmbedWalk_isCycle L q hq
  have hPeven : P.edges.toFinset ∈
      evenSubgraphs (triangularTorusGraph (3 * L)) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph (3 * L)) P hPcycle
  have hQeven : Q.edges.toFinset ∈
      evenSubgraphs (triangularTorusGraph (3 * L)) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph (3 * L)) Q hQcycle
  have hPsubset : P.edges.toFinset ⊆
      (triangularTorusGraph (3 * L)).edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hPeven).1
  have hQsubset : Q.edges.toFinset ⊆
      (triangularTorusGraph (3 * L)).edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hQeven).1
  have hPEvenSquare : triangularSquareExpansion (3 * L) P.edges.toFinset ∈
      evenSubgraphs (onsTorusGraph (3 * L)) :=
    triangularSquareExpansion_evenSubgraph (3 * L) P.edges.toFinset hPeven
  have hQEvenSquare : triangularSquareExpansion (3 * L) Q.edges.toFinset ∈
      evenSubgraphs (onsTorusGraph (3 * L)) :=
    triangularSquareExpansion_evenSubgraph (3 * L) Q.edges.toFinset hQeven
  have hinc : ∀ z,
      incCount (triangularSquareExpansion (3 * L) P.edges.toFinset) z = 0 ∨
      incCount (triangularSquareExpansion (3 * L) Q.edges.toFinset) z = 0 := by
    exact triangularTorusSplitEmbedWalk_squareExpansion_incCount_disjoint
      L p q (triangularTorusSplitEmbedWalk_verts_disjoint
        L p q hdisjoint)
  have hinter : ons_homologyIntersection
      (ons_evenHomology (3 * L)
        (triangularSquareExpansion (3 * L) P.edges.toFinset))
      (ons_evenHomology (3 * L)
        (triangularSquareExpansion (3 * L) Q.edges.toFinset)) = 0 :=
    ons_homologyIntersection_eq_zero_of_incCount_disjoint
      (3 * L) _ _ hPEvenSquare hQEvenSquare hinc
  rw [← triangularTorusSplitEmbedWalk_surfaceHomology L p,
    ← triangularTorusSplitEmbedWalk_surfaceHomology L q,
    triangularTorus_surfaceSubgraphHomology_eq,
    triangularTorus_surfaceSubgraphHomology_eq,
    ← triangularSquareExpansion_evenHomology (3 * L) P.edges.toFinset
      hPsubset,
    ← triangularSquareExpansion_evenHomology (3 * L) Q.edges.toFinset
      hQsubset,
    surfaceIntersection_genus_one_eq_ons]
  exact hinter

end StatMech.FrontierA
