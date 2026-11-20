/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationWeighted










namespace StatMech.Onsager

open StatMech.Ising

theorem ons_originalEdgesOfDecorated_eq_empty_iff
    (L : ℕ) [Fact (2 < L)] (D : ons_DecoratedEvenSubgraph L) :
    ons_originalEdgesOfDecorated L D = ∅ ↔ D.1 = ∅ := by
  classical
  let D0 : ons_DecoratedEvenSubgraph L :=
    ⟨∅, by simp [evenSubgraphs, IsEvenSubgraph, incCount]⟩
  have hD0 : ons_originalEdgesOfDecorated L D0 = ∅ := by
    rw [← ons_decoratedExternalEdges_image L D0]
    simp [ons_decoratedExternalEdges, D0]
  constructor
  · intro hD
    have hinvVal : ((ons_decorationEquiv L).symm D).1 =
        ((ons_decorationEquiv L).symm D0).1 := by
      simpa [ons_originalEdgesOfDecorated] using hD.trans hD0.symm
    have hinv : (ons_decorationEquiv L).symm D =
        (ons_decorationEquiv L).symm D0 := Subtype.ext hinvVal
    have hDD0 : D = D0 := (ons_decorationEquiv L).symm.injective hinv
    simpa [D0] using congrArg Subtype.val hDD0
  · intro hD
    rw [← ons_decoratedExternalEdges_image L D]
    simp [ons_decoratedExternalEdges, hD]

theorem ons_decoratedExternalEdges_nonempty
    (L : ℕ) [Fact (2 < L)] (D : ons_DecoratedEvenSubgraph L)
    (hD : D.1.Nonempty) :
    (ons_decoratedExternalEdges D.1).Nonempty := by
  classical
  by_contra hext
  rw [Finset.not_nonempty_iff_eq_empty] at hext
  have horig : ons_originalEdgesOfDecorated L D = ∅ := by
    rw [← ons_decoratedExternalEdges_image L D, hext]
    simp
  have hDempty := (ons_originalEdgesOfDecorated_eq_empty_iff L D).mp horig
  exact (Finset.nonempty_iff_ne_empty.mp hD) hDempty



theorem ons_decCycle_exists_external
    {L : ℕ} [Fact (2 < L)] {v : ons_Dart L}
    (p : (ons_decGraph L).Walk v v) (hp : p.IsCycle) :
    ∃ d : ons_Dart L,
      s(d, ons_dartRev L d) ∈ p.edges.toFinset := by
  classical
  let D : ons_DecoratedEvenSubgraph L :=
    ⟨p.edges.toFinset, ons_cycle_edges_evenSubgraph (ons_decGraph L) p hp⟩
  have hD : D.1.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hedge
    have hlist : p.edges = [] := (List.toFinset_eq_empty_iff p.edges).mp hedge
    have hnil : p.Nil := SimpleGraph.Walk.edges_eq_nil.mp hlist
    exact hp.not_nil hnil
  obtain ⟨edge, hedge⟩ := ons_decoratedExternalEdges_nonempty L D hD
  have hdata := Finset.mem_filter.mp hedge
  rcases hdata.2 with ⟨d, rfl⟩
  exact ⟨d, hdata.1⟩



theorem ons_decCycle_root_at_external
    {L : ℕ} [Fact (2 < L)] {v : ons_Dart L}
    (p : (ons_decGraph L).Walk v v) (hp : p.IsCycle)
    (d : ons_Dart L)
    (hd : s(d, ons_dartRev L d) ∈ p.edges.toFinset) :
    ∃ q : (ons_decGraph L).Walk d d,
      q.IsCycle ∧ q.snd = ons_dartRev L d ∧
        q.edges.toFinset = p.edges.toFinset := by
  classical
  have hdsupp : d ∈ p.support :=
    p.fst_mem_support_of_mem_edges (List.mem_toFinset.mp hd)
  let q0 := p.rotate d hdsupp
  have hq0 : q0.IsCycle :=
    (SimpleGraph.Walk.isCycle_rotate hdsupp).mpr hp
  have hedge0 : s(d, ons_dartRev L d) ∈ q0.edges := by
    exact (p.rotate_edges d hdsupp).mem_iff.mpr (List.mem_toFinset.mp hd)
  have hsplit : q0.snd = ons_dartRev L d ∨
      q0.penultimate = ons_dartRev L d := by
    have hq0nil : ¬ q0.Nil := hq0.not_nil
    rw [← q0.cons_tail_eq hq0nil,
      SimpleGraph.Walk.edges_cons, List.mem_cons] at hedge0
    rcases hedge0 with hfirst | htail
    · left
      rw [Sym2.eq_iff] at hfirst
      rcases hfirst with hfirst | hfirst
      · exact hfirst.2.symm
      · exact ((ons_dartRev_ne_self L d) hfirst.2).elim
    · right
      have htailPath : q0.tail.IsPath := hq0.isPath_tail
      have hrevPen : ons_dartRev L d = q0.tail.penultimate :=
        htailPath.eq_penultimate_of_mem_edges htail
      have htailnil : ¬ q0.tail.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        have hlen := hq0.three_le_length
        have htailLen := q0.length_tail_add_one hq0nil
        omega
      have hpen : q0.penultimate = q0.tail.penultimate := by
        have h := SimpleGraph.Walk.penultimate_cons_of_not_nil
          (q0.adj_snd hq0nil) q0.tail htailnil
        rw [q0.cons_tail_eq hq0nil] at h
        exact h
      rw [hpen, ← hrevPen]
  have hedgeq0 : q0.edges.toFinset = p.edges.toFinset :=
    List.toFinset_eq_of_perm q0.edges p.edges (p.rotate_edges d hdsupp).perm
  rcases hsplit with hsnd | hpen
  · exact ⟨q0, hq0, hsnd, hedgeq0⟩
  · refine ⟨q0.reverse, hq0.reverse, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.snd_reverse] using hpen
    · rw [SimpleGraph.Walk.edges_reverse, List.toFinset_reverse, hedgeq0]




theorem ons_decCycle_root_external
    {L : ℕ} [Fact (2 < L)] {v : ons_Dart L}
    (p : (ons_decGraph L).Walk v v) (hp : p.IsCycle) :
    ∃ (d : ons_Dart L) (q : (ons_decGraph L).Walk d d),
      q.IsCycle ∧ q.snd = ons_dartRev L d ∧
        q.edges.toFinset = p.edges.toFinset := by
  classical
  obtain ⟨d, hd⟩ := ons_decCycle_exists_external p hp
  have hdsupp : d ∈ p.support :=
    p.fst_mem_support_of_mem_edges (List.mem_toFinset.mp hd)
  let q0 := p.rotate d hdsupp
  have hq0 : q0.IsCycle :=
    (SimpleGraph.Walk.isCycle_rotate hdsupp).mpr hp
  have hedge0 : s(d, ons_dartRev L d) ∈ q0.edges := by
    exact (p.rotate_edges d hdsupp).mem_iff.mpr (List.mem_toFinset.mp hd)
  have hsplit : q0.snd = ons_dartRev L d ∨
      q0.penultimate = ons_dartRev L d := by
    have hq0nil : ¬ q0.Nil := hq0.not_nil
    rw [← q0.cons_tail_eq hq0nil,
      SimpleGraph.Walk.edges_cons, List.mem_cons] at hedge0
    rcases hedge0 with hfirst | htail
    · left
      rw [Sym2.eq_iff] at hfirst
      rcases hfirst with hfirst | hfirst
      · exact hfirst.2.symm
      · exact ((ons_dartRev_ne_self L d) hfirst.2).elim
    · right
      have htailPath : q0.tail.IsPath := hq0.isPath_tail
      have hrevPen : ons_dartRev L d = q0.tail.penultimate :=
        htailPath.eq_penultimate_of_mem_edges htail
      have htailnil : ¬ q0.tail.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        have hlen := hq0.three_le_length
        have htailLen := q0.length_tail_add_one hq0nil
        omega
      have hpen : q0.penultimate = q0.tail.penultimate := by
        have h := SimpleGraph.Walk.penultimate_cons_of_not_nil
          (q0.adj_snd hq0nil) q0.tail htailnil
        rw [q0.cons_tail_eq hq0nil] at h
        exact h
      rw [hpen, ← hrevPen]
  have hedgeq0 : q0.edges.toFinset = p.edges.toFinset :=
    List.toFinset_eq_of_perm q0.edges p.edges (p.rotate_edges d hdsupp).perm
  rcases hsplit with hsnd | hpen
  · exact ⟨d, q0, hq0, hsnd, hedgeq0⟩
  · refine ⟨d, q0.reverse, hq0.reverse, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.snd_reverse] using hpen
    · rw [SimpleGraph.Walk.edges_reverse, List.toFinset_reverse, hedgeq0]

end StatMech.Onsager
