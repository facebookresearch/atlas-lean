/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.RankWidth

/-!
# Rank-width of vertex-minors

Rank-width does not increase under vertex-minors: a vertex-minor of a finite graph of
rank-width at most `k` also has rank-width at most `k`. The proof restricts a
rank-decomposition of the ambient graph to the induced subgraph, pruning the leaves of
deleted vertices and smoothing the resulting degree-two nodes.

## References

* S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100
  (author's revised preprint of 18 April 2005), Corollary 2.7.
-/

@[expose] public section

namespace SimpleGraph

namespace IsVertexMinor

section Prune

/-- **Cut-rank of an induced subgraph.** The cut-rank of a vertex set in a graph obtained by
reindexing along an injective map is at most the cut-rank of the corresponding set in the
ambient graph, since the cut matrix of the former is a submatrix of the cut matrix of the
latter. -/
private theorem cutRank_comap_le {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} (f : β ↪ α)
    (hadj : ∀ x y, H.Adj x y ↔ G.Adj (f x) (f y))
    {X : Set α} {Y : Set β} (hY : Y = f ⁻¹' X) :
    H.cutRank Y ≤ G.cutRank X := by
  subst hY
  classical
  unfold cutRank
  let r : ↥(f ⁻¹' X) → ↥X := fun y => ⟨f y, y.2⟩
  let c : ↥(f ⁻¹' X)ᶜ → ↥Xᶜ := fun z => ⟨f z, fun hx => z.2 (by simp [hx])⟩
  have hmat : (H.adjMatrix (ZMod 2)).submatrix (fun x : ↥(f ⁻¹' X) => (x : β))
        (fun y : ↥(f ⁻¹' X)ᶜ => (y : β)) =
      ((G.adjMatrix (ZMod 2)).submatrix (fun x : ↥X => (x : α))
        (fun y : ↥Xᶜ => (y : α))).submatrix r c := by
    ext i j
    simp only [Matrix.submatrix_apply, r, c]
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply, hadj]
  rw [hmat]
  exact Matrix.rank_submatrix_le _ r c

/-- Deleting one vertex from a finite type removes exactly one element. -/
private theorem card_subtype_ne_add_one {V : Type*} [Fintype V] (v0 : V)
    [Fintype {v : V // v ≠ v0}] :
    Fintype.card {v : V // v ≠ v0} + 1 = Fintype.card V := by
  classical
  have h := Fintype.card_subtype_compl (fun x : V => x = v0)
  have h1 : Fintype.card {x : V // x = v0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨v0, rfl⟩, fun ⟨x, hx⟩ => Subtype.ext hx⟩
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v0⟩
  have h' : Fintype.card {x : V // ¬ x = v0} + 1 = Fintype.card V := by omega
  exact h'


variable {V : Type*} {D : RankDecomposition V} {i0 u a b : D.ι}

private def prunedTree (hab : a ≠ b) : SimpleGraph {i : D.ι // i ≠ i0 ∧ i ≠ u} where
  Adj x y := D.T.Adj x y ∨ (x.1 = a ∧ y.1 = b) ∨ (x.1 = b ∧ y.1 = a)
  symm := ⟨fun x y h => by
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun x h => by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact D.T.loopless.irrefl x h
    · grind
    · grind⟩

private theorem sym2_ne_of_subtype {p q b' c' : D.ι}
    {hb' : b' ≠ i0 ∧ b' ≠ u} {hc' : c' ≠ i0 ∧ c' ≠ u}
    {hp : p ≠ i0 ∧ p ≠ u} {hq : q ≠ i0 ∧ q ≠ u}
    (h : s(b', c') ≠ s(p, q)) :
    (s(⟨b', hb'⟩, ⟨c', hc'⟩) : Sym2 {i : D.ι // i ≠ i0 ∧ i ≠ u}) ≠
      s(⟨p, hp⟩, ⟨q, hq⟩) := by
  intro heq
  apply h
  rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩)

private theorem reachable_pruned_of_reachable_old
    {hab : a ≠ b} {ha0 : a ≠ i0} {hb0 : b ≠ i0} {hau : D.T.Adj a u} {hub : D.T.Adj b u}
    {hN0 : D.T.neighborSet i0 = {u}} {hN : D.T.neighborSet u = {i0, a, b}}
    {hnotab : ¬ D.T.Adj a b}
    {p q : D.ι} (hp : p ≠ i0 ∧ p ≠ u) (hq : q ≠ i0 ∧ q ≠ u) (hpq : D.T.Adj p q)
    {x : D.ι} (hx : x ≠ i0 ∧ x ≠ u) {y : D.ι}
    (h : (D.T.deleteEdges {s(p, q)}).Reachable x y) :
    (∀ hy0 : y ≠ i0, ∀ hyu : y ≠ u,
      ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Reachable ⟨x, hx⟩
        ⟨y, ⟨hy0, hyu⟩⟩) ∧
    (y = u →
      ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Reachable ⟨x, hx⟩
          ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ ∧
        ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Reachable ⟨x, hx⟩
          ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩) ∧
    (y = i0 →
      ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Reachable ⟨x, hx⟩
          ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ ∨
        ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Reachable ⟨x, hx⟩
          ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩) := by
  classical
  have hne_new : (s(⟨a, ⟨ha0, fun h => hau.ne h⟩⟩,
        ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩) : Sym2 {i : D.ι // i ≠ i0 ∧ i ≠ u}) ≠
      s(⟨p, hp⟩, ⟨q, hq⟩) := by
    intro heq
    apply hnotab
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : a = p := congrArg Subtype.val h1
      have e2 : b = q := congrArg Subtype.val h2
      rw [e1, e2]; exact hpq
    · have e1 : a = q := congrArg Subtype.val h1
      have e2 : b = p := congrArg Subtype.val h2
      rw [e1, e2]; exact hpq.symm
  have adj_i0 : ∀ z, D.T.Adj z i0 → z = u := by
    intro z hz
    have hz' : z ∈ D.T.neighborSet i0 := hz.symm
    rw [hN0] at hz'
    exact Set.mem_singleton_iff.mp hz'
  have adj_u : ∀ z, D.T.Adj z u → z = i0 ∨ z = a ∨ z = b := by
    intro z hz
    have hz' : z ∈ D.T.neighborSet u := hz.symm
    rw [hN] at hz'
    simpa using hz'
  have old_step : ∀ {z w : D.ι} (hz : z ≠ i0 ∧ z ≠ u) (hw : w ≠ i0 ∧ w ≠ u),
      D.T.Adj z w → s(z, w) ≠ s(p, q) →
      ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Adj ⟨z, hz⟩ ⟨w, hw⟩ := by
    intro z w hz hw hT hne
    rw [deleteEdges_adj]
    refine ⟨Or.inl hT, ?_⟩
    simp only [Set.mem_singleton_iff]
    exact sym2_ne_of_subtype hne
  have new_ab : ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Adj
      ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ := by
    rw [deleteEdges_adj]
    refine ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    simp only [Set.mem_singleton_iff]
    exact hne_new
  have new_ba : ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Adj
      ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ := by
    rw [deleteEdges_adj]
    refine ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
    simp only [Set.mem_singleton_iff]
    simpa [Sym2.eq_swap] using hne_new
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl =>
    refine ⟨fun _ _ => Reachable.refl _, fun h => absurd h hx.2, fun h => absurd h hx.1⟩
  | tail hbc hstep ih =>
    rename_i mid last
    obtain ⟨hT, hne⟩ := deleteEdges_adj.mp hstep
    simp only [Set.mem_singleton_iff] at hne
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro hy0 hyu
      by_cases hmid0 : mid = i0
      · rw [hmid0] at hT
        exact absurd (adj_i0 _ hT.symm) hyu
      by_cases hmidu : mid = u
      · rw [hmidu] at hT
        rcases adj_u _ hT.symm with rfl | rfl | rfl
        · exact absurd rfl hy0
        · exact (ih2 hmidu).1
        · exact (ih2 hmidu).2
      · exact (ih1 hmid0 hmidu).trans (old_step ⟨hmid0, hmidu⟩ ⟨hy0, hyu⟩ hT hne).reachable
    · intro hyu
      rw [hyu] at hT
      by_cases hmid0 : mid = i0
      · rcases ih3 hmid0 with h | h
        · exact ⟨h, h.trans new_ab.reachable⟩
        · exact ⟨h.trans new_ba.reachable, h⟩
      by_cases hmidu : mid = u
      · rw [hmidu] at hT
        exact absurd hT (D.T.loopless.irrefl _)
      · rcases adj_u _ hT with rfl | rfl | rfl
        · exact absurd rfl hmid0
        · exact ⟨ih1 hmid0 hmidu, (ih1 hmid0 hmidu).trans new_ab.reachable⟩
        · exact ⟨(ih1 hmid0 hmidu).trans new_ba.reachable, ih1 hmid0 hmidu⟩
    · intro hy0
      rw [hy0] at hT
      have hmid : mid = u := adj_i0 _ hT
      exact Or.inl (ih2 hmid).1


private theorem sym2_ne_of_ne {z w p q : D.ι} (h1 : w ≠ p) (h2 : w ≠ q) :
    s(z, w) ≠ s(p, q) := by
  intro heq
  rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
  · exact h2 h
  · exact h1 h

private theorem sym2_ne_of_left_ne {z w p q : D.ι} (h1 : z ≠ p) (h2 : z ≠ q) :
    s(z, w) ≠ s(p, q) := by
  intro heq
  rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
  · exact h1 h
  · exact h2 h

private theorem sym2_of_subtype_eq {z w p q : D.ι}
    {hz : z ≠ i0 ∧ z ≠ u} {hw : w ≠ i0 ∧ w ≠ u}
    {hp : p ≠ i0 ∧ p ≠ u} {hq : q ≠ i0 ∧ q ≠ u}
    (h : (s(⟨z, hz⟩, ⟨w, hw⟩) : Sym2 {i : D.ι // i ≠ i0 ∧ i ≠ u}) = s(⟨p, hp⟩, ⟨q, hq⟩)) :
    s(z, w) = s(p, q) := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩)

private theorem sym2_subtype_eq_of_eq {z w p q : D.ι}
    {hz : z ≠ i0 ∧ z ≠ u} {hw : w ≠ i0 ∧ w ≠ u}
    {hp : p ≠ i0 ∧ p ≠ u} {hq : q ≠ i0 ∧ q ≠ u}
    (h : s(z, w) = s(p, q)) :
    (s(⟨z, hz⟩, ⟨w, hw⟩) : Sym2 {i : D.ι // i ≠ i0 ∧ i ≠ u}) = s(⟨p, hp⟩, ⟨q, hq⟩) := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)

private theorem reachable_of_reachable_pruned_old
    {hab : a ≠ b} {hau : D.T.Adj a u} {hub : D.T.Adj b u}
    {p q : D.ι} (hp : p ≠ i0 ∧ p ≠ u) (hq : q ≠ i0 ∧ q ≠ u)
    {x : D.ι} (hx : x ≠ i0 ∧ x ≠ u) {z : {i : D.ι // i ≠ i0 ∧ i ≠ u}}
    (h : ((prunedTree (D := D) hab).deleteEdges {s(⟨p, hp⟩, ⟨q, hq⟩)}).Reachable ⟨x, hx⟩ z) :
    (D.T.deleteEdges {s(p, q)}).Reachable x z.1 := by
  classical
  rw [reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hbc hstep ih =>
    rename_i mid last
    obtain ⟨hAdj, hne⟩ := deleteEdges_adj.mp hstep
    simp only [Set.mem_singleton_iff] at hne
    refine ih.trans ?_
    rcases hAdj with hT | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Relation.ReflTransGen.single (deleteEdges_adj.mpr ⟨hT, by
        intro heq
        exact hne (sym2_subtype_eq_of_eq heq)⟩)
    · have step1 : (D.T.deleteEdges {s(p, q)}).Adj (mid : D.ι) u := by
        rw [h1]
        exact deleteEdges_adj.mpr ⟨hau, by
          simp only [Set.mem_singleton_iff]
          exact sym2_ne_of_ne hp.2.symm hq.2.symm⟩
      have step2 : (D.T.deleteEdges {s(p, q)}).Adj u (last : D.ι) := by
        rw [h2]
        exact deleteEdges_adj.mpr ⟨hub.symm, by
          simp only [Set.mem_singleton_iff]
          exact sym2_ne_of_left_ne hp.2.symm hq.2.symm⟩
      exact (Relation.ReflTransGen.single step1).trans (Relation.ReflTransGen.single step2)
    · have step1 : (D.T.deleteEdges {s(p, q)}).Adj (mid : D.ι) u := by
        rw [h1]
        exact deleteEdges_adj.mpr ⟨hub, by
          simp only [Set.mem_singleton_iff]
          exact sym2_ne_of_ne hp.2.symm hq.2.symm⟩
      have step2 : (D.T.deleteEdges {s(p, q)}).Adj u (last : D.ι) := by
        rw [h2]
        exact deleteEdges_adj.mpr ⟨hau.symm, by
          simp only [Set.mem_singleton_iff]
          exact sym2_ne_of_left_ne hp.2.symm hq.2.symm⟩
      exact (Relation.ReflTransGen.single step1).trans (Relation.ReflTransGen.single step2)

private theorem sym2_ne_of_ne_u {z w e : D.ι} (hz : z ≠ u) (hw : w ≠ u) :
    s(z, w) ≠ s(e, u) := by
  intro heq
  rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h, _⟩
  · exact hw h
  · exact hz h

private theorem reachable_pruned_of_reachable_new
    {hab : a ≠ b} {ha0 : a ≠ i0} {hb0 : b ≠ i0} {hau : D.T.Adj a u} {hub : D.T.Adj b u}
    {hN0 : D.T.neighborSet i0 = {u}}
    {hnotab : ¬ D.T.Adj a b}
    {s t : D.ι} (hs : s ≠ i0 ∧ s ≠ u) (ht : t ≠ i0 ∧ t ≠ u) (hts : t ≠ s)
    (htu : D.T.Adj t u)
    (hnot : ¬ (D.T.deleteEdges {s(s, u)}).Reachable s t)
    {y : D.ι} (h : (D.T.deleteEdges {s(s, u)}).Reachable s y) :
    y ≠ u ∧ y ≠ i0 ∧ ∀ hy : y ≠ i0 ∧ y ≠ u,
      ((prunedTree (D := D) hab).deleteEdges
        {s(⟨a, ⟨ha0, fun h => hau.ne h⟩⟩, ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩)}).Reachable
        ⟨s, hs⟩ ⟨y, hy⟩ := by
  classical
  have adj_i0 : ∀ z, D.T.Adj z i0 → z = u := by
    intro z hz
    have hz' : z ∈ D.T.neighborSet i0 := hz.symm
    rw [hN0] at hz'
    exact Set.mem_singleton_iff.mp hz'
  have hnotu : ¬ (D.T.deleteEdges {s(s, u)}).Reachable s u := by
    intro hreach
    apply hnot
    refine hreach.trans (deleteEdges_adj.mpr ⟨htu.symm, ?_⟩).reachable
    simp only [Set.mem_singleton_iff]
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
    · exact ht.2 h
    · exact hts h
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨hs.2, hs.1, fun _ => Reachable.refl _⟩
  | tail hbc hstep ih =>
    rename_i mid last
    obtain ⟨hT, hne⟩ := deleteEdges_adj.mp hstep
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · by_cases hlu : last = u
      · exfalso
        apply hnotu
        have hreach : (D.T.deleteEdges {s(s, u)}).Reachable s last :=
          (reachable_iff_reflTransGen _ _).mpr
            (hbc.trans (Relation.ReflTransGen.single hstep))
        rwa [hlu] at hreach
      · exact hlu
    · by_cases hli : last = i0
      · exfalso
        rw [hli] at hT
        exact ih1 (adj_i0 _ hT)
      · exact hli
    · intro hy
      by_cases hlu : last = u
      · exfalso
        apply hnotu
        have hreach : (D.T.deleteEdges {s(s, u)}).Reachable s last :=
          (reachable_iff_reflTransGen _ _).mpr
            (hbc.trans (Relation.ReflTransGen.single hstep))
        rwa [hlu] at hreach
      by_cases hli : last = i0
      · exfalso
        rw [hli] at hT
        exact ih1 (adj_i0 _ hT)
      by_cases hmidu : mid = u
      · exact absurd hmidu ih1
      by_cases hmidi0 : mid = i0
      · exact absurd hmidi0 ih2
      · have hne_ab : s(mid, last) ≠ s(a, b) := by
          intro heq
          apply hnotab
          rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2] at hT; exact hT
          · rw [h1, h2] at hT; exact hT.symm
        have hstep' : ((prunedTree (D := D) hab).deleteEdges
            {s(⟨a, ⟨ha0, fun h => hau.ne h⟩⟩, ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩)}).Adj
            ⟨mid, ⟨hmidi0, hmidu⟩⟩ ⟨last, hy⟩ := by
          rw [deleteEdges_adj]
          refine ⟨Or.inl hT, ?_⟩
          simp only [Set.mem_singleton_iff]
          exact sym2_ne_of_subtype hne_ab
        exact (ih3 ⟨hmidi0, hmidu⟩).trans hstep'.reachable

private theorem reachable_of_reachable_pruned_new
    {hab : a ≠ b} {ha0 : a ≠ i0} {hb0 : b ≠ i0} {hau : D.T.Adj a u} {hub : D.T.Adj b u}
    {s : D.ι}
    {x : D.ι} (hx : x ≠ i0 ∧ x ≠ u) {z : {i : D.ι // i ≠ i0 ∧ i ≠ u}}
    (h : ((prunedTree (D := D) hab).deleteEdges
      {s(⟨a, ⟨ha0, fun h => hau.ne h⟩⟩, ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩)}).Reachable
      ⟨x, hx⟩ z) :
    (D.T.deleteEdges {s(s, u)}).Reachable x z.1 := by
  classical
  rw [reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hbc hstep ih =>
    rename_i mid last
    obtain ⟨hAdj, hne⟩ := deleteEdges_adj.mp hstep
    simp only [Set.mem_singleton_iff] at hne
    refine ih.trans ?_
    rcases hAdj with hT | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Relation.ReflTransGen.single (deleteEdges_adj.mpr ⟨hT, by
        simp only [Set.mem_singleton_iff]
        exact sym2_ne_of_ne_u mid.2.2 last.2.2⟩)
    · exfalso
      exact hne (Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩))
    · exfalso
      exact hne (Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩))

private theorem reachable_pruned_of_reachable
    {hab : a ≠ b} {ha0 : a ≠ i0} {hb0 : b ≠ i0} {hau : D.T.Adj a u} {hub : D.T.Adj b u}
    {hN0 : D.T.neighborSet i0 = {u}} {hN : D.T.neighborSet u = {i0, a, b}}
    {x : D.ι} (hx : x ≠ i0 ∧ x ≠ u) {y : D.ι}
    (h : D.T.Reachable x y) :
    (∀ hy0 : y ≠ i0, ∀ hyu : y ≠ u,
      (prunedTree (D := D) hab).Reachable ⟨x, hx⟩ ⟨y, ⟨hy0, hyu⟩⟩) ∧
    (y = u →
      (prunedTree (D := D) hab).Reachable ⟨x, hx⟩ ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ ∧
        (prunedTree (D := D) hab).Reachable ⟨x, hx⟩ ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩) ∧
    (y = i0 →
      (prunedTree (D := D) hab).Reachable ⟨x, hx⟩ ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ ∨
        (prunedTree (D := D) hab).Reachable ⟨x, hx⟩ ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩) := by
  classical
  have adj_i0 : ∀ z, D.T.Adj z i0 → z = u := by
    intro z hz
    have hz' : z ∈ D.T.neighborSet i0 := hz.symm
    rw [hN0] at hz'
    exact Set.mem_singleton_iff.mp hz'
  have adj_u : ∀ z, D.T.Adj z u → z = i0 ∨ z = a ∨ z = b := by
    intro z hz
    have hz' : z ∈ D.T.neighborSet u := hz.symm
    rw [hN] at hz'
    simpa using hz'
  have new_ab : (prunedTree (D := D) hab).Adj ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩
      ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have new_ba : (prunedTree (D := D) hab).Adj ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩
      ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ := Or.inr (Or.inr ⟨rfl, rfl⟩)
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl =>
    refine ⟨fun _ _ => Reachable.refl _, fun h => absurd h hx.2, fun h => absurd h hx.1⟩
  | tail hbc hstep ih =>
    rename_i mid last
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro hy0 hyu
      by_cases hmid0 : mid = i0
      · rw [hmid0] at hstep
        exact absurd (adj_i0 _ hstep.symm) hyu
      by_cases hmidu : mid = u
      · rw [hmidu] at hstep
        rcases adj_u _ hstep.symm with rfl | rfl | rfl
        · exact absurd rfl hy0
        · exact (ih2 hmidu).1
        · exact (ih2 hmidu).2
      · exact (ih1 hmid0 hmidu).trans (show (prunedTree (D := D) hab).Adj
          ⟨mid, ⟨hmid0, hmidu⟩⟩ ⟨last, ⟨hy0, hyu⟩⟩ from Or.inl hstep).reachable
    · intro hyu
      rw [hyu] at hstep
      by_cases hmid0 : mid = i0
      · rcases ih3 hmid0 with h | h
        · exact ⟨h, h.trans new_ab.reachable⟩
        · exact ⟨h.trans new_ba.reachable, h⟩
      by_cases hmidu : mid = u
      · rw [hmidu] at hstep
        exact absurd hstep (D.T.loopless.irrefl _)
      · rcases adj_u _ hstep with rfl | rfl | rfl
        · exact absurd rfl hmid0
        · exact ⟨ih1 hmid0 hmidu, (ih1 hmid0 hmidu).trans new_ab.reachable⟩
        · exact ⟨(ih1 hmid0 hmidu).trans new_ba.reachable, ih1 hmid0 hmidu⟩
    · intro hy0
      rw [hy0] at hstep
      have hmid : mid = u := adj_i0 _ hstep
      exact Or.inl (ih2 hmid).1

private theorem not_reachable_deleteEdges_of_adj_u
    {s t : D.ι} (hsu : D.T.Adj s u) (htu : D.T.Adj t u) (hts : t ≠ s) (hsu_ne : s ≠ u) :
    ¬ (D.T.deleteEdges {s(s, u)}).Reachable s t := by
  intro hreach
  rw [reachable_deleteEdges_iff_exists_walk] at hreach
  obtain ⟨p, hp⟩ := hreach
  have hbr : D.T.IsBridge s(s, u) :=
    isAcyclic_iff_forall_adj_isBridge.mp D.isTree.isAcyclic hsu
  have hne : s(s, u) ≠ s(t, u) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hts h1.symm
    · exact hsu_ne h1
  have hmem := (isBridge_iff_forall_walk_mem_edges.mp hbr)
    (p.append (Walk.cons htu Walk.nil))
  simp [Walk.edges_append, Walk.edges_cons, hp, hne] at hmem


/-- The neighbours of a node in the pruned tree are the neighbours in the original tree, with
the smoothed node removed and, at its two other neighbours, replaced by the new edge. In
particular the number of neighbours is unchanged. -/
private theorem neighborSet_pruned_ncard
    {hab : a ≠ b} {ha0 : a ≠ i0} {hb0 : b ≠ i0} {hau : D.T.Adj a u} {hub : D.T.Adj b u}
    {hN0 : D.T.neighborSet i0 = {u}} {hN : D.T.neighborSet u = {i0, a, b}}
    {hnotab : ¬ D.T.Adj a b}
    (x : {i : D.ι // i ≠ i0 ∧ i ≠ u}) :
    ((prunedTree (D := D) hab).neighborSet x).ncard = (D.T.neighborSet x.1).ncard := by
  classical
  haveI := D.fintype
  have adj_i0 : ∀ z, D.T.Adj z i0 → z = u := by
    intro z hz
    have hz' : z ∈ D.T.neighborSet i0 := hz.symm
    rw [hN0] at hz'
    exact Set.mem_singleton_iff.mp hz'
  have adj_u : ∀ z, D.T.Adj z u → z = i0 ∨ z = a ∨ z = b := by
    intro z hz
    have hz' : z ∈ D.T.neighborSet u := hz.symm
    rw [hN] at hz'
    simpa using hz'
  have hpre : ∀ (f : {i : D.ι // i ≠ i0 ∧ i ≠ u} → D.ι), Function.Injective f →
      ∀ S : Set D.ι, S ⊆ Set.range f → (f ⁻¹' S).ncard = S.ncard := by
    intro f hf S hS
    rw [← Set.ncard_image_of_injective _ hf]
    congr 1
    exact Set.image_preimage_eq_of_subset hS
  by_cases hxa : x.1 = a
  · obtain rfl : x = ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ := Subtype.ext hxa
    change ((prunedTree (D := D) hab).neighborSet ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩).ncard =
      (D.T.neighborSet a).ncard
    have huN : u ∈ D.T.neighborSet a := hau
    have hset : (prunedTree (D := D) hab).neighborSet ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ =
        Subtype.val ⁻¹' (D.T.neighborSet a \ {u}) ∪
          {⟨b, ⟨hb0, fun h => hub.ne h⟩⟩} := by
      ext y
      constructor
      · intro hy
        rcases hy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Set.mem_union_left _ ⟨h, fun hh => y.2.2 (Set.mem_singleton_iff.mp hh)⟩
        · exact Set.mem_union_right _ (Subtype.ext h2)
        · exact absurd h1 hab
      · intro hy
        rcases hy with hy | hy
        · exact Or.inl hy.1
        · rw [hy]
          exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have hdisj : (⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ :
        {i : D.ι // i ≠ i0 ∧ i ≠ u}) ∉ Subtype.val ⁻¹' (D.T.neighborSet a \ {u}) := by
      intro hbmem
      exact hnotab hbmem.1
    have hsub : D.T.neighborSet a \ {u} ⊆ Set.range
        (Subtype.val : {i : D.ι // i ≠ i0 ∧ i ≠ u} → D.ι) := by
      intro z hz
      refine ⟨⟨z, ⟨?_, hz.2⟩⟩, rfl⟩
      intro hzi
      have hz' : D.T.Adj a z := hz.1
      rw [hzi] at hz'
      exact hau.ne (adj_i0 _ hz')
    rw [hset, Set.union_singleton, Set.ncard_insert_of_notMem hdisj,
      hpre _ Subtype.val_injective _ hsub, Set.ncard_sdiff_singleton_of_mem huN]
    rcases D.degree_one_or_three a with h1 | h3 <;> omega
  · by_cases hxb : x.1 = b
    · obtain rfl : x = ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ := Subtype.ext hxb
      change ((prunedTree (D := D) hab).neighborSet ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩).ncard =
        (D.T.neighborSet b).ncard
      have huN : u ∈ D.T.neighborSet b := hub
      have hnotab' : ¬ D.T.Adj b a := fun h => hnotab h.symm
      have hset : (prunedTree (D := D) hab).neighborSet ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ =
          Subtype.val ⁻¹' (D.T.neighborSet b \ {u}) ∪
            {⟨a, ⟨ha0, fun h => hau.ne h⟩⟩} := by
        ext y
        constructor
        · intro hy
          rcases hy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Set.mem_union_left _ ⟨h, fun hh => y.2.2 (Set.mem_singleton_iff.mp hh)⟩
          · exact absurd h1.symm hab
          · exact Set.mem_union_right _ (Subtype.ext h2)
        · intro hy
          rcases hy with hy | hy
          · exact Or.inl hy.1
          · rw [hy]
            exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      have hdisj : (⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ :
          {i : D.ι // i ≠ i0 ∧ i ≠ u}) ∉ Subtype.val ⁻¹' (D.T.neighborSet b \ {u}) := by
        intro hamem
        exact hnotab' hamem.1
      have hsub : D.T.neighborSet b \ {u} ⊆ Set.range
          (Subtype.val : {i : D.ι // i ≠ i0 ∧ i ≠ u} → D.ι) := by
        intro z hz
        refine ⟨⟨z, ⟨?_, hz.2⟩⟩, rfl⟩
        intro hzi
        have hz' : D.T.Adj b z := hz.1
        rw [hzi] at hz'
        exact hub.ne (adj_i0 _ hz')
      rw [hset, Set.union_singleton, Set.ncard_insert_of_notMem hdisj,
        hpre _ Subtype.val_injective _ hsub, Set.ncard_sdiff_singleton_of_mem huN]
      rcases D.degree_one_or_three b with h1 | h3 <;> omega
    · have hset : (prunedTree (D := D) hab).neighborSet x =
          Subtype.val ⁻¹' (D.T.neighborSet x.1) := by
        ext y
        constructor
        · intro hy
          rcases hy with h | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h
          · exact absurd h1 hxa
          · exact absurd h1 hxb
        · intro hy
          exact Or.inl hy
      have hsub : D.T.neighborSet x.1 ⊆ Set.range
          (Subtype.val : {i : D.ι // i ≠ i0 ∧ i ≠ u} → D.ι) := by
        intro z hz
        have hz' : D.T.Adj x.1 z := hz
        refine ⟨⟨z, ⟨?_, ?_⟩⟩, rfl⟩
        · intro hzi
          rw [hzi] at hz'
          exact x.2.2 (adj_i0 _ hz')
        · intro hzu
          rw [hzu] at hz'
          rcases adj_u _ hz' with h | h | h
          · exact x.2.1 h
          · exact hxa h
          · exact hxb h
      rw [hset, hpre _ Subtype.val_injective _ hsub]

/-- Deleting the edge `s(x, y)` or the edge `s(y, x)` gives the same graph. -/
private theorem reachable_deleteEdges_sym2 {ι : Type*} {G' : SimpleGraph ι} {x y u v : ι}
    (h : (G'.deleteEdges {s(x, y)}).Reachable u v) :
    (G'.deleteEdges {s(y, x)}).Reachable u v := by
  rwa [Sym2.eq_swap] at h

/-- **Pruning a rank-decomposition.** Deleting one vertex from a graph with a
rank-decomposition of width at most `k` leaves a rank-decomposition of the induced
subgraph on the remaining vertices, of the same width: the leaf of the deleted vertex and
its neighbour are removed from the decomposition tree, and the neighbour's other two
neighbours are joined. -/
private theorem prune_decomposition {G : SimpleGraph V} [Fintype V] (D : RankDecomposition V)
    {k : ℕ} (hw : D.HasWidthAtMost G k) (v0 : V) [Fintype {x : V // x ≠ v0}]
    (hcard : 2 ≤ Fintype.card {x : V // x ≠ v0}) :
    ∃ D' : RankDecomposition {x : V // x ≠ v0},
      D'.HasWidthAtMost (G.induce {x : V | x ≠ v0}) k := by
  classical
  haveI := D.fintype
  have hcardV : 3 ≤ Fintype.card V := by
    have hcard' : 2 ≤ Fintype.card {x : V // x ≠ v0} := hcard
    have h := card_subtype_ne_add_one (V := V) v0
    omega
  set i0 : D.ι := D.leaf v0 with hi0def
  have hi0deg : (D.T.neighborSet i0).ncard = 1 := by
    have hmem : i0 ∈ Set.range D.leaf := ⟨v0, rfl⟩
    rwa [D.range_leaf] at hmem
  obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp hi0deg
  have hiu : D.T.Adj i0 u := by
    have hmem : u ∈ D.T.neighborSet i0 := by
      rw [hu]
      exact Set.mem_singleton u
    exact hmem
  have hdeg_u : (D.T.neighborSet u).ncard = 3 := by
    rcases D.degree_one_or_three u with h1 | h3
    · exfalso
      have hNu : D.T.neighborSet u = {i0} := by
        obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp h1
        have hi0mem : i0 ∈ D.T.neighborSet u := hiu.symm
        rw [hz] at hi0mem
        rw [hz, (Set.mem_singleton_iff.mp hi0mem).symm]
      have hmem : ∀ z : D.ι, D.T.Reachable i0 z → z = i0 ∨ z = u := by
        intro z hz
        rw [reachable_iff_reflTransGen] at hz
        induction hz with
        | refl => exact Or.inl rfl
        | tail hbc hstep ih =>
          rename_i mid last
          rcases ih with hmid | hmid
          · rw [hmid] at hstep
            have hlast : last ∈ D.T.neighborSet i0 := hstep
            rw [hu] at hlast
            exact Or.inr (Set.mem_singleton_iff.mp hlast)
          · rw [hmid] at hstep
            have hlast : last ∈ D.T.neighborSet u := hstep
            rw [hNu] at hlast
            exact Or.inl (Set.mem_singleton_iff.mp hlast)
      have hrange : Set.range D.leaf ⊆ {i0, u} := by
        intro z hz
        obtain ⟨w, rfl⟩ := hz
        exact hmem _ (D.isTree.connected i0 _)
      have hcardle : Fintype.card V ≤ 2 := by
        have h1 : Fintype.card V = Fintype.card ↥(Set.range D.leaf) :=
          Fintype.card_congr (Equiv.ofInjective D.leaf D.leaf.injective)
        rw [h1]
        have h2 : Fintype.card ↥(Set.range D.leaf) ≤ Fintype.card ↥({i0, u} : Set D.ι) :=
          Fintype.card_le_of_injective (fun z => ⟨z.1, hrange z.2⟩)
            (fun a b h => Subtype.ext (congrArg
              (fun z : ↥({i0, u} : Set D.ι) => (z : D.ι)) h))
        have h3 : Fintype.card ↥({i0, u} : Set D.ι) ≤ 2 := by
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
          have h := Set.ncard_insert_le (a := i0) (s := ({u} : Set D.ι))
          rw [Set.ncard_singleton] at h
          exact h
        exact le_trans h2 h3
      omega
    · exact h3
  have h2 : (D.T.neighborSet u \ {i0}).ncard = 2 := by
    have hi0mem : i0 ∈ D.T.neighborSet u := hiu.symm
    rw [Set.ncard_sdiff_singleton_of_mem hi0mem, hdeg_u]
  obtain ⟨a, b, hab, hpair⟩ := Set.ncard_eq_two.mp h2
  have ha_mem : a ∈ D.T.neighborSet u \ {i0} := by rw [hpair]; simp
  have hb_mem : b ∈ D.T.neighborSet u \ {i0} := by rw [hpair]; simp
  have hau' : D.T.Adj u a := ha_mem.1
  have hub' : D.T.Adj u b := hb_mem.1
  have hau : D.T.Adj a u := hau'.symm
  have hub : D.T.Adj b u := hub'.symm
  have ha0 : a ≠ i0 := fun h => ha_mem.2 (Set.mem_singleton_iff.mpr h)
  have hb0 : b ≠ i0 := fun h => hb_mem.2 (Set.mem_singleton_iff.mpr h)
  have hN : D.T.neighborSet u = {i0, a, b} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      by_cases hzi : z = i0
      · exact Or.inl hzi
      · have hz' : z ∈ D.T.neighborSet u \ {i0} :=
          ⟨hz, fun h => hzi (Set.mem_singleton_iff.mp h)⟩
        rw [hpair] at hz'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
        rcases hz' with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact hiu.symm
      · exact hau'
      · exact hub'
  have hnotab : ¬ D.T.Adj a b := by
    intro hab'
    have hbr : D.T.IsBridge s(a, u) :=
      isAcyclic_iff_forall_adj_isBridge.mp D.isTree.isAcyclic hau
    have hmem := (isBridge_iff_forall_walk_mem_edges.mp hbr)
      (Walk.cons hab' (Walk.cons hub Walk.nil))
    simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with h | h
    · rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hub.ne h2.symm
      · exact hab h1
    · rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab h1
      · exact hau.ne h1
  have leaf_ne_i0 : ∀ w : {x : V // x ≠ v0}, D.leaf w.1 ≠ i0 := by
    intro w h
    exact w.2 (D.leaf.injective h)
  have leaf_ne_u : ∀ w : {x : V // x ≠ v0}, D.leaf w.1 ≠ u := by
    intro w h
    have hmem : (D.T.neighborSet u).ncard = 1 := by
      have hmem : u ∈ Set.range D.leaf := ⟨w.1, h⟩
      rwa [D.range_leaf] at hmem
    omega
  let leafEmb : {x : V // x ≠ v0} ↪ {i : D.ι // i ≠ i0 ∧ i ≠ u} :=
    ⟨fun w => ⟨D.leaf w.1, ⟨leaf_ne_i0 w, leaf_ne_u w⟩⟩,
      fun a b h => Subtype.ext (D.leaf.injective (congrArg Subtype.val h))⟩
  have hIsTree : (prunedTree (D := D) (i0 := i0) (u := u) hab).IsTree := by
    refine (isTree_iff _).mpr ⟨?_, ?_⟩
    · refine Connected.mk (G := prunedTree (D := D) (i0 := i0) (u := u) hab)
        (fun x y => (reachable_pruned_of_reachable (hab := hab) (ha0 := ha0) (hb0 := hb0)
          (hau := hau) (hub := hub) (hN0 := hu) (hN := hN) x.2
          (D.isTree.connected x.1 y.1)).1 y.2.1 y.2.2)
        (nonempty := ⟨⟨a, ⟨ha0, fun h => hau.ne h⟩⟩⟩)
    · rw [isAcyclic_iff_forall_adj_isBridge]
      intro x y hAdj
      rcases hAdj with hT | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [isBridge_iff]
        intro hreach
        have hbr : D.T.IsBridge s(x.1, y.1) :=
          isAcyclic_iff_forall_adj_isBridge.mp D.isTree.isAcyclic hT
        exact (isBridge_iff.mp hbr)
          (reachable_of_reachable_pruned_old (hab := hab) (hau := hau) (hub := hub)
            x.2 y.2 x.2 hreach)
      · have hx : x = ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ := Subtype.ext h1
        have hy : y = ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ := Subtype.ext h2
        subst hx
        subst hy
        rw [isBridge_iff]
        intro hreach
        have hnot : ¬ (D.T.deleteEdges {s(a, u)}).Reachable a b :=
          not_reachable_deleteEdges_of_adj_u hau hub hab.symm hau.ne
        exact hnot (reachable_of_reachable_pruned_new (hab := hab) (ha0 := ha0)
          (hb0 := hb0) (hau := hau) (hub := hub) ⟨ha0, fun h => hau.ne h⟩ hreach)
      · have hx : x = ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ := Subtype.ext h1
        have hy : y = ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ := Subtype.ext h2
        subst hx
        subst hy
        rw [isBridge_iff]
        intro hreach
        have hnot : ¬ (D.T.deleteEdges {s(b, u)}).Reachable b a :=
          not_reachable_deleteEdges_of_adj_u hub hau hab hub.ne
        exact hnot (reachable_of_reachable_pruned_new (hab := hab) (ha0 := ha0)
          (hb0 := hb0) (hau := hau) (hub := hub) ⟨hb0, fun h => hub.ne h⟩
          (reachable_deleteEdges_sym2 hreach))
  have hdeg : ∀ x : {i : D.ι // i ≠ i0 ∧ i ≠ u},
      ((prunedTree hab).neighborSet x).ncard = 1 ∨
        ((prunedTree hab).neighborSet x).ncard = 3 := by
    intro x
    rw [neighborSet_pruned_ncard (hab := hab) (ha0 := ha0) (hb0 := hb0) (hau := hau)
      (hub := hub) (hN0 := hu) (hN := hN) (hnotab := hnotab) x]
    exact D.degree_one_or_three x.1
  have hrange : Set.range leafEmb =
      {i | ((prunedTree hab).neighborSet i).ncard = 1} := by
    ext i
    constructor
    · rintro ⟨w, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [neighborSet_pruned_ncard (hab := hab) (ha0 := ha0) (hb0 := hb0) (hau := hau)
        (hub := hub) (hN0 := hu) (hN := hN) (hnotab := hnotab)]
      have hmem : D.leaf w.1 ∈ Set.range D.leaf := ⟨w.1, rfl⟩
      rwa [D.range_leaf] at hmem
    · intro hi
      have hiT : (D.T.neighborSet i.1).ncard = 1 := by
        rw [← neighborSet_pruned_ncard (hab := hab) (ha0 := ha0) (hb0 := hb0) (hau := hau)
          (hub := hub) (hN0 := hu) (hN := hN) (hnotab := hnotab) i]
        exact hi
      have hmem : i.1 ∈ Set.range D.leaf := by
        rw [D.range_leaf]
        exact hiT
      obtain ⟨w, hw⟩ := hmem
      have hw0 : w ≠ v0 := fun h => i.2.1 (by rw [← hw, h])
      exact ⟨⟨w, hw0⟩, Subtype.ext hw⟩
  let D' : RankDecomposition {x : V // x ≠ v0} :=
    { ι := {i : D.ι // i ≠ i0 ∧ i ≠ u}
      T := prunedTree hab
      isTree := hIsTree
      degree_one_or_three := hdeg
      leaf := leafEmb
      range_leaf := hrange }
  refine ⟨D', ?_⟩
  intro i j hij
  have hcut : ∀ {X : Set V} {Y : Set {x : V // x ≠ v0}},
      Y = (fun w : {x : V // x ≠ v0} => w.1) ⁻¹' X → G.cutRank X ≤ k →
      (G.induce {x : V | x ≠ v0}).cutRank Y ≤ k := by
    intro X Y hY hX
    rw [hY]
    exact (cutRank_comap_le (⟨Subtype.val, Subtype.val_injective⟩ :
      {x : V // x ≠ v0} ↪ V) (fun _ _ => Iff.rfl) rfl).trans hX
  rcases hij with hT | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hside : D'.side i j = (fun w : {x : V // x ≠ v0} => w.1) ⁻¹' (D.side i.1 j.1) := by
      ext w
      simp only [RankDecomposition.side, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · intro hreach
        exact reachable_of_reachable_pruned_old (hab := hab) (hau := hau) (hub := hub)
          i.2 j.2 i.2 hreach
      · intro hreach
        exact (reachable_pruned_of_reachable_old (hab := hab) (ha0 := ha0) (hb0 := hb0)
          (hau := hau) (hub := hub) (hN0 := hu) (hN := hN) (hnotab := hnotab)
          i.2 j.2 hT i.2 hreach).1 (leaf_ne_i0 w) (leaf_ne_u w)
    exact hcut hside (hw i.1 j.1 hT)
  · have hx : i = ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ := Subtype.ext h1
    have hy : j = ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ := Subtype.ext h2
    subst hx
    subst hy
    have hnot : ¬ (D.T.deleteEdges {s(a, u)}).Reachable a b :=
      not_reachable_deleteEdges_of_adj_u hau hub hab.symm hau.ne
    have hside : D'.side ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ =
        (fun w : {x : V // x ≠ v0} => w.1) ⁻¹' (D.side a u) := by
      ext w
      simp only [RankDecomposition.side, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · intro hreach
        exact reachable_of_reachable_pruned_new (hab := hab) (ha0 := ha0) (hb0 := hb0)
          (hau := hau) (hub := hub) ⟨ha0, fun h => hau.ne h⟩ hreach
      · intro hreach
        exact (reachable_pruned_of_reachable_new (hab := hab) (ha0 := ha0) (hb0 := hb0)
          (hau := hau) (hub := hub) (hN0 := hu) (hnotab := hnotab)
          ⟨ha0, fun h => hau.ne h⟩ ⟨hb0, fun h => hub.ne h⟩
          hab.symm hub hnot hreach).2.2 ⟨leaf_ne_i0 w, leaf_ne_u w⟩
    exact hcut hside (hw a u hau)
  · have hx : i = ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ := Subtype.ext h1
    have hy : j = ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ := Subtype.ext h2
    subst hx
    subst hy
    have hnot : ¬ (D.T.deleteEdges {s(b, u)}).Reachable b a :=
      not_reachable_deleteEdges_of_adj_u hub hau hab hub.ne
    have hside : D'.side ⟨b, ⟨hb0, fun h => hub.ne h⟩⟩ ⟨a, ⟨ha0, fun h => hau.ne h⟩⟩ =
        (fun w : {x : V // x ≠ v0} => w.1) ⁻¹' (D.side b u) := by
      ext w
      simp only [RankDecomposition.side, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · intro hreach
        exact reachable_of_reachable_pruned_new (hab := hab) (ha0 := ha0) (hb0 := hb0)
          (hau := hau) (hub := hub) ⟨hb0, fun h => hub.ne h⟩
          (reachable_deleteEdges_sym2 hreach)
      · intro hreach
        exact reachable_deleteEdges_sym2
          ((reachable_pruned_of_reachable_new (hab := hab) (ha0 := ha0) (hb0 := hb0)
            (hau := hau) (hub := hub) (hN0 := hu) (hnotab := hnotab)
            ⟨hb0, fun h => hub.ne h⟩ ⟨ha0, fun h => hau.ne h⟩
            hab hau hnot hreach).2.2 ⟨leaf_ne_i0 w, leaf_ne_u w⟩)
    exact hcut hside (hw b u hub)

end Prune


/-- **Rank-width is preserved by renaming the vertices.** If two graphs are related by a
vertex bijection, a rank-decomposition of one transports to the other with the same width. -/
private theorem hasRankWidthAtMost_of_equiv {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} (e : β ≃ α)
    (hadj : ∀ x y, H.Adj x y ↔ G.Adj (e x) (e y)) {k : ℕ}
    (h : G.HasRankWidthAtMost k) : H.HasRankWidthAtMost k := by
  classical
  by_cases hsmall : Fintype.card β ≤ 1
  · exact Or.inl hsmall
  · push Not at hsmall
    have hcardα : ¬ Fintype.card α ≤ 1 := by
      rw [← Fintype.card_congr e]
      omega
    rcases h with hsmallα | ⟨D, hw⟩
    · exact absurd hsmallα hcardα
    · haveI := D.fintype
      have hrange : Set.range (e.toEmbedding.trans D.leaf) =
          {i | (D.T.neighborSet i).ncard = 1} := by
        ext i
        simp only [Set.mem_range, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨w, rfl⟩
          have hi : D.leaf (e w) ∈ Set.range D.leaf := ⟨e w, rfl⟩
          rwa [D.range_leaf] at hi
        · intro hi
          have hi' : i ∈ Set.range D.leaf := by rwa [D.range_leaf]
          obtain ⟨v, hv⟩ := hi'
          exact ⟨e.symm v, by simp [hv]⟩
      refine Or.inr ⟨⟨D.ι, D.T, D.isTree, D.degree_one_or_three,
        e.toEmbedding.trans D.leaf, hrange⟩, ?_⟩
      intro i j hij
      exact (cutRank_comap_le e.toEmbedding hadj rfl).trans (hw i j hij)

/-- **Deleting a vertex does not increase rank-width.** The induced subgraph on the
remaining vertices inherits a rank-decomposition of the same width, by pruning. -/
private theorem hasRankWidthAtMost_delete {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (h : G.HasRankWidthAtMost k) (v0 : V) [Fintype {x : V // x ≠ v0}] :
    (G.induce {x : V | x ≠ v0}).HasRankWidthAtMost k := by
  classical
  by_cases hsmall : Fintype.card {x : V // x ≠ v0} ≤ 1
  · exact Or.inl hsmall
  · push Not at hsmall
    rcases h with hsmallV | ⟨D, hw⟩
    · have hle : Fintype.card {x : V // x ≠ v0} ≤ Fintype.card V :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      omega
    · obtain ⟨D', hw'⟩ := prune_decomposition D hw v0 (by omega)
      exact Or.inr ⟨D', hw'⟩

/-- **Vertex-minors of a graph on at most `n` vertices.** Induction on the number of
vertices: if the embedding is surjective, rename the vertices; otherwise delete a vertex
outside its range and apply the induction hypothesis to the induced subgraph. -/
private theorem hasRankWidthAtMost_comap_aux (k : ℕ) (n : ℕ) :
    ∀ {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph V)
      {H : SimpleGraph W} (f : W ↪ V), H = G.comap f → Fintype.card V ≤ n →
      G.HasRankWidthAtMost k → H.HasRankWidthAtMost k := by
  induction n with
  | zero =>
    intro V W _ _ G H f hH hcard hG
    have hle : Fintype.card W ≤ Fintype.card V := Fintype.card_le_of_injective f f.injective
    exact Or.inl (by omega)
  | succ n ih =>
    intro V W _ _ G H f hH hcard hG
    classical
    by_cases hsurj : Function.Surjective f
    · refine hasRankWidthAtMost_of_equiv (Equiv.ofBijective f ⟨f.injective, hsurj⟩) ?_ hG
      intro x y
      rw [hH]
      exact Iff.rfl
    · simp only [Function.Surjective, not_forall, not_exists] at hsurj
      obtain ⟨v0, hv0⟩ := hsurj
      let f1 : W ↪ {v : V // v ≠ v0} :=
        ⟨fun w => ⟨f w, hv0 w⟩, fun a b h => f.injective (congrArg Subtype.val h)⟩
      have hH1 : H = (G.induce {v : V | v ≠ v0}).comap f1 := by
        ext x y
        rw [hH]
        exact Iff.rfl
      have hG1 : (G.induce {v : V | v ≠ v0}).HasRankWidthAtMost k :=
        hasRankWidthAtMost_delete hG v0
      have hcard1 : Fintype.card {v : V // v ≠ v0} ≤ n := by
        have h := card_subtype_ne_add_one (V := V) v0
        omega
      exact ih (G.induce {v : V | v ≠ v0}) f1 hH1 hcard1 hG1

end IsVertexMinor

variable {V : Type*} [Fintype V]

/-- **Rank-width does not increase under vertex-minors.** If `H` is a vertex-minor of the finite
graph `G` and `G` has rank-width at most `k`, then so does `H` (Oum, *Rank-width and
vertex-minors*, J. Combin. Theory Ser. B 95 (2005), Corollary 2.7, second statement: local
complementation preserves cut-rank and vertex deletion does not increase it). -/
theorem IsVertexMinor.hasRankWidthAtMost {W : Type*} [Fintype W] {H : SimpleGraph W}
    {G : SimpleGraph V} (h : H.IsVertexMinor G) {k : ℕ} (hG : G.HasRankWidthAtMost k) :
    H.HasRankWidthAtMost k := by
  obtain ⟨G', hloc, f, rfl⟩ := h
  have hG' : G'.HasRankWidthAtMost k :=
    (LocallyEquivalent.hasRankWidthAtMost_iff hloc k).mpr hG
  exact hasRankWidthAtMost_comap_aux k (Fintype.card V) G' f rfl (le_refl _) hG'

end SimpleGraph
