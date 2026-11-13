/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWExtremalTraceContact











open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box


noncomputable def rlc_extremalSelectionCounterexampleConfig :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => e ∈
    rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
      rlc_pathEdges rlc_traceSplitCounterexampleLeft.1



theorem rlc_path_eq_of_edges_subset {V : Type*} {G : SimpleGraph V}
    {u v : V} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hedges : ∀ e ∈ q.edges, e ∈ p.edges) : q = p := by
  induction p with
  | nil =>
      have h := congrArg Subtype.val
        (SimpleGraph.Path.loop_eq ⟨q, hq⟩)
      simpa using h
  | @cons u w v huw p ih =>
      cases q with
      | nil => simp at hp
      | @cons _ z _ huz q =>
          have huzMem : s(u, z) ∈ (SimpleGraph.Walk.cons huw p).edges :=
            hedges _ (by simp)
          have huzSub : (SimpleGraph.Walk.cons huw p).toSubgraph.Adj u z := by
            rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
            exact huzMem
          have hwz := hp.snd_of_toSubgraph_adj huzSub
          simp only [SimpleGraph.Walk.snd_cons] at hwz
          subst z
          congr 1
          apply ih q hp.of_cons hq.of_cons
          intro e he
          have he' := hedges e (by simp [he])
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he'
          rcases he' with heFirst | heTail
          · subst e
            exact False.elim
              (((SimpleGraph.Walk.isTrail_cons huz q).mp hq.isTrail).2 he)
          · exact heTail

theorem rlc_extremalSelectionConfig_right_edges {e : Sym2 (Site 2)}
    (heOpen : rlc_extremalSelectionCounterexampleConfig e = true)
    (heRect : ∀ x y : Site 2, e = s(x, y) →
      x ∈ rect 0 2 (-1) 1 ∧ y ∈ rect 0 2 (-1) 1) :
    e ∈ rlc_pathEdges rlc_traceSplitCounterexampleRight.1 := by
  classical
  have heUnion : e ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
    simpa [rlc_extremalSelectionCounterexampleConfig] using heOpen
  rcases Finset.mem_union.mp heUnion with heRight | heLeft
  · exact heRight
  · induction e using Sym2.inductionOn with
    | _ x y =>
        have hxyRect := heRect x y rfl
        have hxyAdj := rlc_pathEdge_lattice
          rlc_traceSplitCounterexampleLeft.1 heLeft
        have hxyLeft :=
          rlc_pathEdge_endpoints_mem_vertices
            rlc_traceSplitCounterexampleLeft.1 heLeft
        rw [rlc_traceSplitCounterexample_left_vertices] at hxyLeft
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxyLeft
        rw [mem_rect, mem_rect] at hxyRect
        rcases hxyLeft.1 with rfl | rfl | rfl | rfl <;>
          rcases hxyLeft.2 with rfl | rfl | rfl | rfl <;>
          simp_all

theorem rlc_extremalSelectionConfig_left_edges {e : Sym2 (Site 2)}
    (heOpen : rlc_extremalSelectionCounterexampleConfig e = true)
    (heRect : ∀ x y : Site 2, e = s(x, y) →
      x ∈ rect (-2) 0 (-1) 1 ∧ y ∈ rect (-2) 0 (-1) 1) :
    e ∈ rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
  classical
  have heUnion : e ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
    simpa [rlc_extremalSelectionCounterexampleConfig] using heOpen
  rcases Finset.mem_union.mp heUnion with heRight | heLeft
  · induction e using Sym2.inductionOn with
    | _ x y =>
        have hxyRect := heRect x y rfl
        have hxyAdj := rlc_pathEdge_lattice
          rlc_traceSplitCounterexampleRight.1 heRight
        have hxyRight :=
          rlc_pathEdge_endpoints_mem_vertices
            rlc_traceSplitCounterexampleRight.1 heRight
        rw [rlc_traceSplitCounterexample_right_vertices] at hxyRight
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxyRight
        rw [mem_rect, mem_rect] at hxyRect
        rcases hxyRight.1 with rfl | rfl | rfl | rfl <;>
          rcases hxyRight.2 with rfl | rfl | rfl | rfl <;>
          simp_all
  · exact heLeft

theorem rlc_extremalSelection_open_right_edges_subset
    (delta : RlcRightDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    rlc_pathEdges delta.1 ⊆
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      apply rlc_extremalSelectionConfig_right_edges (hopen s(x, y) he)
      intro a b hab
      have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 he
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rlc_pathVertex_mem_rect delta.1 hends.1,
          rlc_pathVertex_mem_rect delta.1 hends.2⟩
      · exact ⟨rlc_pathVertex_mem_rect delta.1 hends.2,
          rlc_pathVertex_mem_rect delta.1 hends.1⟩

theorem rlc_extremalSelection_open_left_edges_subset
    (delta : RlcLeftDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    rlc_pathEdges delta.1 ⊆
      rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      apply rlc_extremalSelectionConfig_left_edges (hopen s(x, y) he)
      intro a b hab
      have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 he
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rlc_pathVertex_mem_rect delta.1 hends.1,
          rlc_pathVertex_mem_rect delta.1 hends.2⟩
      · exact ⟨rlc_pathVertex_mem_rect delta.1 hends.2,
          rlc_pathVertex_mem_rect delta.1 hends.1⟩

theorem rlc_extremalSelection_open_right_start
    (delta : RlcRightDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    (delta.1.1 : Site 2) = ![0, -1] := by
  let q := delta.1.2.2.1
  have hne : (⟨delta.1.1, leftSide_subset delta.1.1.2⟩ :
      rect 0 2 (-1) 1) ≠
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
    intro h
    have h0 := congrArg (fun z : rect 0 2 (-1) 1 => (z : Site 2) 0) h
    have hx := delta.1.1.2.2
    have hy := delta.1.2.1.2.2
    norm_num at h0 hx hy
    omega
  obtain ⟨z, hz, tail, hq⟩ := q.exists_eq_cons_of_ne hne
  have heDelta : s((delta.1.1 : Site 2), (z : Site 2)) ∈
      rlc_pathEdges delta.1 := by
    rw [rlc_pathEdges, Finset.mem_image]
    refine ⟨s(⟨delta.1.1, leftSide_subset delta.1.1.2⟩, z), ?_, rfl⟩
    change s(⟨delta.1.1, leftSide_subset delta.1.1.2⟩, z) ∈
      q.edges.toFinset
    rw [hq]
    apply List.mem_toFinset.mpr
    simp
  have heRight := rlc_extremalSelection_open_right_edges_subset
    delta hopen heDelta
  have hstart :=
    (rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleRight.1 heRight).1
  rw [rlc_traceSplitCounterexample_right_vertices] at hstart
  simp only [Finset.mem_insert, Finset.mem_singleton] at hstart
  have hx := delta.1.1.2.2
  rcases hstart with h | h | h | h <;> simp_all

theorem rlc_extremalSelection_open_right_end
    (delta : RlcRightDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    (delta.1.2.1 : Site 2) = ![2, 0] := by
  let q := delta.1.2.2.1
  have hne : (⟨delta.1.1, leftSide_subset delta.1.1.2⟩ :
      rect 0 2 (-1) 1) ≠
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
    intro h
    have h0 := congrArg (fun z : rect 0 2 (-1) 1 => (z : Site 2) 0) h
    have hx := delta.1.1.2.2
    have hy := delta.1.2.1.2.2
    norm_num at h0 hx hy
    omega
  have hqNot : ¬ q.Nil := q.not_nil_of_ne hne
  have hz := q.toSubgraph_adj_penultimate hqNot
  have hzEdge : s((q.penultimate : Site 2),
      (delta.1.2.1 : Site 2)) ∈ rlc_pathEdges delta.1 := by
    rw [rlc_pathEdges, Finset.mem_image]
    refine ⟨s(q.penultimate,
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩), ?_, rfl⟩
    change s(q.penultimate,
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩) ∈
        q.edges.toFinset
    simpa only [List.mem_toFinset] using
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hz
  have heRight := rlc_extremalSelection_open_right_edges_subset
    delta hopen hzEdge
  have hend :=
    (rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleRight.1 heRight).2
  rw [rlc_traceSplitCounterexample_right_vertices] at hend
  simp only [Finset.mem_insert, Finset.mem_singleton] at hend
  have hy := delta.1.2.1.2.2
  have hupp := delta.2.2
  simp [rlc_upperHalf] at hupp
  rcases hend with h | h | h | h <;> simp_all

theorem rlc_extremalSelection_right_unique
    (delta : RlcRightDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    delta = rlc_traceSplitCounterexampleRight := by
  have hxVal := rlc_extremalSelection_open_right_start delta hopen
  have hyVal := rlc_extremalSelection_open_right_end delta hopen
  have hxTarget :
      (rlc_traceSplitCounterexampleRight.1.1 : Site 2) = ![0, -1] := by
    have h := rlc_path_start_mem_vertices
      rlc_traceSplitCounterexampleRight.1
    rw [rlc_traceSplitCounterexample_right_vertices] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have hx := rlc_traceSplitCounterexampleRight.1.1.2.2
    rcases h with h | h | h | h <;> simp_all
  have hyTarget :
      (rlc_traceSplitCounterexampleRight.1.2.1 : Site 2) = ![2, 0] := by
    have h : (rlc_traceSplitCounterexampleRight.1.2.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices _ _).1
        (rlc_ambientCrossingWalk _).end_mem_support
    rw [rlc_traceSplitCounterexample_right_vertices] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have hy := rlc_traceSplitCounterexampleRight.1.2.1.2.2
    have hupp := rlc_traceSplitCounterexampleRight.2.2
    simp [rlc_upperHalf] at hupp
    rcases h with h | h | h | h <;> simp_all
  have hx : delta.1.1 = rlc_traceSplitCounterexampleRight.1.1 := by
    apply Subtype.ext
    exact hxVal.trans hxTarget.symm
  have hy : delta.1.2.1 = rlc_traceSplitCounterexampleRight.1.2.1 := by
    apply Subtype.ext
    exact hyVal.trans hyTarget.symm
  rcases delta with ⟨⟨x, y, p⟩, hd⟩
  dsimp only at hx hy ⊢
  subst x
  subst y
  apply Subtype.ext
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  apply Subtype.ext
  apply rlc_path_eq_of_edges_subset _ _
    rlc_traceSplitCounterexampleRight.1.2.2.2 p.2
  intro e he
  have heDelta : Sym2.map Subtype.val e ∈
      rlc_pathEdges ⟨rlc_traceSplitCounterexampleRight.1.1,
        rlc_traceSplitCounterexampleRight.1.2.1, p⟩ := by
    rw [rlc_pathEdges, Finset.mem_image]
    exact ⟨e, List.mem_toFinset.mpr he, rfl⟩
  have heRight := rlc_extremalSelection_open_right_edges_subset
    ⟨⟨rlc_traceSplitCounterexampleRight.1.1,
      rlc_traceSplitCounterexampleRight.1.2.1, p⟩, hd⟩ hopen heDelta
  rw [rlc_pathEdges, Finset.mem_image] at heRight
  obtain ⟨f, hf, hfe⟩ := heRight
  have hef : e = f := Sym2.map.injective Subtype.val_injective hfe.symm
  exact hef ▸ List.mem_toFinset.mp hf

theorem rlc_extremalSelection_open_left_start
    (delta : RlcLeftDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    (delta.1.1 : Site 2) = ![-2, 0] := by
  let q := delta.1.2.2.1
  have hne : (⟨delta.1.1, leftSide_subset delta.1.1.2⟩ :
      rect (-2) 0 (-1) 1) ≠
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
    intro h
    have h0 := congrArg
      (fun z : rect (-2) 0 (-1) 1 => (z : Site 2) 0) h
    have hx := delta.1.1.2.2
    have hy := delta.1.2.1.2.2
    norm_num at h0 hx hy
    omega
  obtain ⟨z, hz, tail, hq⟩ := q.exists_eq_cons_of_ne hne
  have heDelta : s((delta.1.1 : Site 2), (z : Site 2)) ∈
      rlc_pathEdges delta.1 := by
    rw [rlc_pathEdges, Finset.mem_image]
    refine ⟨s(⟨delta.1.1, leftSide_subset delta.1.1.2⟩, z), ?_, rfl⟩
    change s(⟨delta.1.1, leftSide_subset delta.1.1.2⟩, z) ∈
      q.edges.toFinset
    rw [hq]
    apply List.mem_toFinset.mpr
    simp
  have heLeft := rlc_extremalSelection_open_left_edges_subset
    delta hopen heDelta
  have hstart :=
    (rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleLeft.1 heLeft).1
  rw [rlc_traceSplitCounterexample_left_vertices] at hstart
  simp only [Finset.mem_insert, Finset.mem_singleton] at hstart
  have hx := delta.1.1.2.2
  have hlow := delta.2.1
  simp [rlc_lowerHalf] at hlow
  rcases hstart with h | h | h | h <;> simp_all

theorem rlc_extremalSelection_open_left_end
    (delta : RlcLeftDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    (delta.1.2.1 : Site 2) = ![0, 1] := by
  let q := delta.1.2.2.1
  have hne : (⟨delta.1.1, leftSide_subset delta.1.1.2⟩ :
      rect (-2) 0 (-1) 1) ≠
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩ := by
    intro h
    have h0 := congrArg
      (fun z : rect (-2) 0 (-1) 1 => (z : Site 2) 0) h
    have hx := delta.1.1.2.2
    have hy := delta.1.2.1.2.2
    norm_num at h0 hx hy
    omega
  have hqNot : ¬ q.Nil := q.not_nil_of_ne hne
  have hz := q.toSubgraph_adj_penultimate hqNot
  have hzEdge : s((q.penultimate : Site 2),
      (delta.1.2.1 : Site 2)) ∈ rlc_pathEdges delta.1 := by
    rw [rlc_pathEdges, Finset.mem_image]
    refine ⟨s(q.penultimate,
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩), ?_, rfl⟩
    change s(q.penultimate,
      ⟨delta.1.2.1, rightSide_subset delta.1.2.1.2⟩) ∈
        q.edges.toFinset
    simpa only [List.mem_toFinset] using
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hz
  have heLeft := rlc_extremalSelection_open_left_edges_subset
    delta hopen hzEdge
  have hend :=
    (rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleLeft.1 heLeft).2
  rw [rlc_traceSplitCounterexample_left_vertices] at hend
  simp only [Finset.mem_insert, Finset.mem_singleton] at hend
  have hy := delta.1.2.1.2.2
  rcases hend with h | h | h | h <;> simp_all

theorem rlc_extremalSelection_left_unique
    (delta : RlcLeftDiagonalPath 1)
    (hopen : rlc_extremalSelectionCounterexampleConfig ∈
      rlc_pathOpen delta.1) :
    delta = rlc_traceSplitCounterexampleLeft := by
  have hxVal := rlc_extremalSelection_open_left_start delta hopen
  have hyVal := rlc_extremalSelection_open_left_end delta hopen
  have hxTarget :
      (rlc_traceSplitCounterexampleLeft.1.1 : Site 2) = ![-2, 0] := by
    have h := rlc_path_start_mem_vertices
      rlc_traceSplitCounterexampleLeft.1
    rw [rlc_traceSplitCounterexample_left_vertices] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have hx := rlc_traceSplitCounterexampleLeft.1.1.2.2
    have hlow := rlc_traceSplitCounterexampleLeft.2.1
    simp [rlc_lowerHalf] at hlow
    rcases h with h | h | h | h <;> simp_all
  have hyTarget :
      (rlc_traceSplitCounterexampleLeft.1.2.1 : Site 2) = ![0, 1] := by
    have h : (rlc_traceSplitCounterexampleLeft.1.2.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices _ _).1
        (rlc_ambientCrossingWalk _).end_mem_support
    rw [rlc_traceSplitCounterexample_left_vertices] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have hy := rlc_traceSplitCounterexampleLeft.1.2.1.2.2
    rcases h with h | h | h | h <;> simp_all
  have hx : delta.1.1 = rlc_traceSplitCounterexampleLeft.1.1 := by
    apply Subtype.ext
    exact hxVal.trans hxTarget.symm
  have hy : delta.1.2.1 = rlc_traceSplitCounterexampleLeft.1.2.1 := by
    apply Subtype.ext
    exact hyVal.trans hyTarget.symm
  rcases delta with ⟨⟨x, y, p⟩, hd⟩
  dsimp only at hx hy ⊢
  subst x
  subst y
  apply Subtype.ext
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  apply Subtype.ext
  apply rlc_path_eq_of_edges_subset _ _
    rlc_traceSplitCounterexampleLeft.1.2.2.2 p.2
  intro e he
  have heDelta : Sym2.map Subtype.val e ∈
      rlc_pathEdges ⟨rlc_traceSplitCounterexampleLeft.1.1,
        rlc_traceSplitCounterexampleLeft.1.2.1, p⟩ := by
    rw [rlc_pathEdges, Finset.mem_image]
    exact ⟨e, List.mem_toFinset.mpr he, rfl⟩
  have heLeft := rlc_extremalSelection_open_left_edges_subset
    ⟨⟨rlc_traceSplitCounterexampleLeft.1.1,
      rlc_traceSplitCounterexampleLeft.1.2.1, p⟩, hd⟩ hopen heDelta
  rw [rlc_pathEdges, Finset.mem_image] at heLeft
  obtain ⟨f, hf, hfe⟩ := heLeft
  have hef : e = f := Sym2.map.injective Subtype.val_injective hfe.symm
  exact hef ▸ List.mem_toFinset.mp hf

theorem rlc_extremalSelection_rightLowestCandidate :
    rlc_extremalSelectionCounterexampleConfig ∈
      rlc_rightLowestCandidate rlc_traceSplitCounterexampleRight := by
  constructor
  · intro e he
    simpa [rlc_extremalSelectionCounterexampleConfig] using
      (Finset.mem_union_left
        (rlc_pathEdges rlc_traceSplitCounterexampleLeft.1) he)
  · intro hbelowOpen
    obtain ⟨delta, hdelta⟩ := Set.mem_iUnion.mp hbelowOpen
    by_cases hbelow : rlc_rightPathBelow delta
        rlc_traceSplitCounterexampleRight
    · have hopen : rlc_extremalSelectionCounterexampleConfig ∈
          rlc_pathOpen delta.1 := by
        simpa [hbelow] using hdelta
      have heq := rlc_extremalSelection_right_unique delta hopen
      subst delta
      exact rlc_rightPathBelow_irrefl
        rlc_traceSplitCounterexampleRight hbelow
    · simp [hbelow] at hdelta

theorem rlc_extremalSelection_leftHighestCandidate :
    rlc_extremalSelectionCounterexampleConfig ∈
      rlc_leftHighestCandidate rlc_traceSplitCounterexampleLeft := by
  constructor
  · intro e he
    simpa [rlc_extremalSelectionCounterexampleConfig] using
      (Finset.mem_union_right
        (rlc_pathEdges rlc_traceSplitCounterexampleRight.1) he)
  · intro haboveOpen
    obtain ⟨delta, hdelta⟩ := Set.mem_iUnion.mp haboveOpen
    by_cases habove : rlc_leftPathAbove delta
        rlc_traceSplitCounterexampleLeft
    · have hopen : rlc_extremalSelectionCounterexampleConfig ∈
          rlc_pathOpen delta.1 := by
        simpa [habove] using hdelta
      have heq := rlc_extremalSelection_left_unique delta hopen
      subst delta
      exact rlc_leftPathAbove_irrefl
        rlc_traceSplitCounterexampleLeft habove
    · simp [habove] at hdelta

theorem rlc_extremalSelection_extremalPairCandidate :
    rlc_extremalSelectionCounterexampleConfig ∈
      rlc_extremalPairCandidate
        (rlc_traceSplitCounterexampleRight,
          rlc_traceSplitCounterexampleLeft) :=
  ⟨rlc_extremalSelection_rightLowestCandidate,
    rlc_extremalSelection_leftHighestCandidate⟩




theorem rlc_extremalSelection_and_independent_contact_obstruction :
    rlc_extremalSelectionCounterexampleConfig ∈
        rlc_extremalPairCandidate
          (rlc_traceSplitCounterexampleRight,
            rlc_traceSplitCounterexampleLeft) ∧
      rlc_windingSideCounterexampleConfig ∉
        rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧
      ¬ RlcLowestHighestReflectedBoundaryContact
        rlc_windingSideCounterexampleGap
        rlc_windingSideCounterexampleConfig :=
  ⟨rlc_extremalSelection_extremalPairCandidate,
    rlc_windingSideCounterexample_failure,
    rlc_windingSideCounterexample_not_reflectedBoundaryContact⟩

end Universality
end StatMech
