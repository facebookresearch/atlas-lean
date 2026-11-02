/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.KonigMatchingCoverWanted

/-!
# Kőnig's theorem — matching-cover equality

Finite bipartite: max matching size = min vertex cover size.
Source: D. Kőnig, Mat. Fiz. Lapok 38 (1931); J. Egerváry (1931).
-/

/-- Every set in a finite type is finite. -/
private lemma konig_fin {V : Type*} [Finite V] (s : Set V) : s.Finite :=
  Set.finite_univ.subset (Set.subset_univ s)

/-- A matching whose vertices split as `s ∪ t` with every edge across has
`edgeSet.ncard = s.ncard`. -/
private lemma konig_count {V : Type*} {G : SimpleGraph V}
    {S T : Set V} {M : G.Subgraph}
    (hdisj : Disjoint S T) (hM : M.IsMatching) (hverts : M.verts = S ∪ T)
    (hcross : ∀ v w : V, M.Adj v w → (v ∈ S ∧ w ∈ T) ∨ (v ∈ T ∧ w ∈ S)) :
    S.ncard = M.edgeSet.ncard := by
  have hmem : ∀ v : V, v ∈ S → v ∈ M.verts := by
    intro v hv
    simp only [hverts, Set.mem_union]
    exact Or.inl hv
  have hpart : ∀ v : V, ∀ _hv : v ∈ S, (hM (hmem v _hv)).choose ∈ T := by
    intro v hv
    rcases hcross v _ (hM (hmem v hv)).choose_spec.1 with ⟨_, hwt⟩ | ⟨hvt, _⟩
    · exact hwt
    · exact absurd hvt (Set.disjoint_left.mp hdisj hv)
  refine Set.ncard_congr
    (fun v (hv : v ∈ S) => Sym2.mk v (hM (hmem v hv)).choose) ?_ ?_ ?_
  · intro v hv
    exact SimpleGraph.Subgraph.mem_edgeSet.mpr (hM (hmem v hv)).choose_spec.1
  · intro a b ha hb hab
    have hbmem : b ∈ Sym2.mk a (hM (hmem a ha)).choose := by
      rw [hab]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    rcases Sym2.mem_iff.mp hbmem with rfl | hba
    · rfl
    · subst hba
      exfalso
      exact Set.disjoint_left.mp hdisj hb (hpart a ha)
  · intro e he
    obtain ⟨a, b⟩ := e
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he
    rcases hcross a b he with ⟨ha, _⟩ | ⟨_, hb⟩
    · refine ⟨a, ha, ?_⟩
      have huniq := (hM (hmem a ha)).choose_spec.2 b he
      subst huniq
      rfl
    · refine ⟨b, hb, ?_⟩
      have huniq := (hM (hmem b hb)).choose_spec.2 a he.symm
      subst huniq
      exact Sym2.eq_swap

/-- Bridge from a set-level Hall condition to the finset Hall condition. -/
private lemma konig_hall_bridge {V : Type*} [DecidableEq V] {G : SimpleGraph V} {A D : Set V}
    (t : ↥A → Finset V) (ht : ∀ v : ↥A, (↑(t v) : Set V) = G.neighborSet ↑v \ D)
    (hcond : ∀ s : Set V, s ⊆ A → s.ncard ≤ (⋃ x ∈ s, G.neighborSet x \ D).ncard) :
    ∀ c : Finset ↥A, c.card ≤ (c.biUnion t).card := by
  intro c
  set s : Set V := ↑(c.map ⟨Subtype.val, Subtype.val_injective⟩) with hs
  have hsc : s ⊆ A := by
    intro y hy
    rw [hs, Finset.coe_map] at hy
    obtain ⟨v, hvc, rfl⟩ := hy
    exact v.property
  have key : (↑(c.biUnion t) : Set V) = ⋃ x ∈ s, G.neighborSet x \ D := by
    ext x
    simp only [Finset.coe_biUnion, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨v, hvc, hxv⟩
      rw [ht v, Set.mem_sdiff] at hxv
      refine ⟨↑v, ?_, hxv.1, hxv.2⟩
      rw [hs, Finset.coe_map]
      exact Set.mem_image_of_mem _ hvc
    · rintro ⟨y, hy, hxy, hxD⟩
      rw [hs, Finset.coe_map] at hy
      obtain ⟨v, hvc, rfl⟩ := hy
      refine ⟨v, hvc, ?_⟩
      rw [ht v]
      exact (Set.mem_sdiff _).mpr ⟨hxy, hxD⟩
  have e1 : c.card = s.ncard := by
    simp only [hs, Set.ncard_coe_finset, Finset.card_map]
  have e2 : (c.biUnion t).card = (⋃ x ∈ s, G.neighborSet x \ D).ncard := by
    rw [← Set.ncard_coe_finset, key]
  have h1 := hcond s hsc
  omega

/-- Hall-type matching builder: saturate `A` into `B`. -/
private lemma konig_hall_match {V : Type*} [DecidableEq V] {G : SimpleGraph V} {P Q A B : Set V}
    (hPQ : Disjoint P Q) (hsubA : A ⊆ P) (hsubB : B ⊆ Q)
    (hbip : ∀ v w : V, G.Adj v w → (v ∈ P ∧ w ∈ Q) ∨ (v ∈ Q ∧ w ∈ P))
    (t : ↥A → Finset V)
    (htmem : ∀ v : ↥A, ∀ x : V, x ∈ t v → G.Adj (v : V) x ∧ x ∈ B)
    (hHall : ∀ c : Finset ↥A, c.card ≤ (c.biUnion t).card) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = A.ncard ∧ M.verts ⊆ A ∪ B := by
  obtain ⟨g, hginj, hgmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  set r : Set V := Set.range g with hr
  have hrB : r ⊆ B := by
    intro x hx
    obtain ⟨v, rfl⟩ := hx
    exact (htmem v (g v) (hgmem v)).2
  have hdisj : Disjoint A r :=
    Set.disjoint_left.mpr (fun x hxA hxr =>
      Set.disjoint_left.mp hPQ (hsubA hxA) (hsubB (hrB hxr)))
  have hadj : ∀ v : ↥A, G.Adj (v : V) ((Equiv.ofInjective g hginj v : ↥r) : V) := by
    intro v
    have hvv : ((Equiv.ofInjective g hginj v : ↥r) : V) = g v := rfl
    rw [hvv]
    exact (htmem v (g v) (hgmem v)).1
  obtain ⟨M, hverts, hM⟩ :=
    SimpleGraph.Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hdisj
      (Equiv.ofInjective g hginj) hadj
  have hcross : ∀ v w : V, M.Adj v w → (v ∈ A ∧ w ∈ r) ∨ (v ∈ r ∧ w ∈ A) := by
    intro v w hvw
    have hG : G.Adj v w := M.adj_sub hvw
    have hvM : v ∈ M.verts :=
      SimpleGraph.Subgraph.mem_verts_of_mem_edge
        (SimpleGraph.Subgraph.mem_edgeSet.mpr hvw) (Sym2.mem_iff.mpr (Or.inl rfl))
    have hwM : w ∈ M.verts :=
      SimpleGraph.Subgraph.mem_verts_of_mem_edge
        (SimpleGraph.Subgraph.mem_edgeSet.mpr hvw) (Sym2.mem_iff.mpr (Or.inr rfl))
    rw [hverts, Set.mem_union] at hvM hwM
    rcases hbip v w hG with ⟨hvP, hwQ⟩ | ⟨hvQ, hwP⟩
    · rcases hvM with hvA | hvr
      · have hwA : w ∉ A := fun h => Set.disjoint_left.mp hPQ (hsubA h) hwQ
        rcases hwM with hwA' | hwr
        · exact absurd hwA' hwA
        · exact Or.inl ⟨hvA, hwr⟩
      · exfalso
        exact Set.disjoint_left.mp hPQ hvP (hsubB (hrB hvr))
    · rcases hwM with hwA | hwr
      · have hvA : v ∉ A := fun h => Set.disjoint_left.mp hPQ (hsubA h) hvQ
        rcases hvM with hvA' | hvr
        · exact absurd hvA' hvA
        · exact Or.inr ⟨hvr, hwA⟩
      · exfalso
        exact Set.disjoint_left.mp hPQ hwP (hsubB (hrB hwr))
  refine ⟨M, hM, (konig_count hdisj hM hverts hcross).symm, ?_⟩
  rw [hverts]
  intro x hx
  rw [Set.mem_union] at hx ⊢
  rcases hx with hxA | hxr
  · exact Or.inl hxA
  · exact Or.inr (hrB hxr)

/-- **Kőnig's theorem on a finite vertex type.** Let $G$ be a bipartite simple graph on a finite
vertex type $V$. Then there are a matching $M$ in $G$ and a vertex cover $C \subseteq V$ of $G$ such
that the number of edges of $M$ equals the number of vertices in $C$. -/
theorem konig_matching_cover_general {V : Type*} [Finite V] (G : SimpleGraph V)
    (hBip : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V),
      M.IsMatching ∧ G.IsVertexCover C ∧ M.edgeSet.ncard = C.ncard := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨L, R, hLR⟩ := SimpleGraph.IsBipartite.exists_isBipartiteWith hBip
  obtain ⟨Sstar, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun S : {S : Set V // S ⊆ L} => (S.val.ncard : ℤ) - ((⋃ x ∈ S.val, G.neighborSet x).ncard : ℤ))
    ⟨⟨∅, Set.empty_subset _⟩, Finset.mem_univ _⟩
  set Sstarv : Set V := Sstar.val with hSstarv
  set NstarU : Set V := ⋃ x ∈ Sstarv, G.neighborSet x with hNstarU
  set A : Set V := L \ Sstarv with hA
  set B : Set V := R \ NstarU with hB
  have hSsL : Sstarv ⊆ L := Sstar.property
  have hmem : ∀ v w : V, G.Adj v w → (v ∈ L ∧ w ∈ R) ∨ (v ∈ R ∧ w ∈ L) :=
    fun v w h => hLR.mem_of_adj h
  have hNR : NstarU ⊆ R := by
    intro y hy
    simp only [hNstarU, Set.mem_iUnion, exists_prop, SimpleGraph.mem_neighborSet] at hy
    obtain ⟨x, hxS, hxy⟩ := hy
    have hxL : x ∈ L := hSsL hxS
    rcases hmem x y hxy with ⟨_, hyR⟩ | ⟨hxR, _⟩
    · exact hyR
    · exact absurd hxR (Set.disjoint_left.mp hLR.disjoint hxL)
  have hNmem : ∀ (S : Set V) (y : V),
      y ∈ (⋃ x ∈ S, G.neighborSet x) ↔ ∃ x ∈ S, G.Adj x y := by
    intro S y
    simp only [Set.mem_iUnion, exists_prop, SimpleGraph.mem_neighborSet]
  have hmax' : ∀ S : Set V, S ⊆ L →
      (S.ncard : ℤ) - ((⋃ x ∈ S, G.neighborSet x).ncard : ℤ) ≤
      (Sstarv.ncard : ℤ) - (NstarU.ncard : ℤ) :=
    fun S hS => hmax ⟨S, hS⟩ (Finset.mem_univ _)
  have hsubAL : A ⊆ L := Set.sdiff_subset
  have hsubBR : B ⊆ R := Set.sdiff_subset
  -- Hall condition on the `A` side, avoiding `NstarU`.
  have Hset1 : ∀ s : Set V, s ⊆ A →
      s.ncard ≤ (⋃ x ∈ s, G.neighborSet x \ NstarU).ncard := by
    intro s hs
    have hDsL : Sstarv ∪ s ⊆ L :=
      Set.union_subset hSsL (fun x hx => ((Set.mem_sdiff _).mp (hs hx)).1)
    have hle := hmax' (Sstarv ∪ s) hDsL
    have hdisjSs : Disjoint Sstarv s := by
      rw [Set.disjoint_left]
      intro x hxS hxs
      exact ((Set.mem_sdiff _).mp (hs hxs)).2 hxS
    have e1 : (Sstarv ∪ s).ncard = Sstarv.ncard + s.ncard :=
      Set.ncard_union_eq hdisjSs (konig_fin _) (konig_fin _)
    have hNun : (⋃ x ∈ Sstarv ∪ s, G.neighborSet x)
        = (⋃ x ∈ Sstarv, G.neighborSet x) ∪ ⋃ x ∈ s, G.neighborSet x := by
      ext y
      simp only [Set.mem_iUnion, exists_prop, Set.mem_union]
      constructor
      · rintro ⟨x, hx | hxs, hxy⟩
        · exact Or.inl ⟨x, hx, hxy⟩
        · exact Or.inr ⟨x, hxs, hxy⟩
      · rintro (⟨x, hx, hxy⟩ | ⟨x, hxs, hxy⟩)
        · exact ⟨x, Or.inl hx, hxy⟩
        · exact ⟨x, Or.inr hxs, hxy⟩
    have hun : (⋃ x ∈ Sstarv, G.neighborSet x) ∪ (⋃ x ∈ s, G.neighborSet x)
        = NstarU ∪ ((⋃ x ∈ s, G.neighborSet x) \ NstarU) := by
      ext y
      simp only [Set.mem_union, Set.mem_sdiff]
      tauto
    have hdisjN : Disjoint NstarU ((⋃ x ∈ s, G.neighborSet x) \ NstarU) :=
      Set.disjoint_left.mpr (fun y hy1 hy2 => ((Set.mem_sdiff _).mp hy2).2 hy1)
    have e2 : (⋃ x ∈ Sstarv ∪ s, G.neighborSet x).ncard
        = NstarU.ncard + ((⋃ x ∈ s, G.neighborSet x \ NstarU).ncard) := by
      have heq : (⋃ x ∈ s, G.neighborSet x \ NstarU)
          = (⋃ x ∈ s, G.neighborSet x) \ NstarU := by
        ext y
        simp only [Set.mem_iUnion, exists_prop, Set.mem_sdiff]
        constructor
        · rintro ⟨x, hx, hxy, hyN⟩
          exact ⟨⟨x, hx, hxy⟩, hyN⟩
        · rintro ⟨⟨x, hx, hxy⟩, hyN⟩
          exact ⟨x, hx, hxy, hyN⟩
      rw [hNun, hun, heq]
      exact Set.ncard_union_eq hdisjN (konig_fin _) (konig_fin _)
    omega
  -- Hall condition on the `NstarU` side, inside `Sstarv`.
  have Hset2 : ∀ s : Set V, s ⊆ NstarU →
      s.ncard ≤ (⋃ x ∈ s, G.neighborSet x \ Sstarvᶜ).ncard := by
    intro s hs
    have hDsL : Sstarv \ (⋃ x ∈ s, G.neighborSet x) ⊆ L :=
      fun x hx => hSsL ((Set.mem_sdiff _).mp hx).1
    have hle := hmax' _ hDsL
    have hsub : (⋃ x ∈ s, G.neighborSet x) ∩ Sstarv ⊆ Sstarv := Set.inter_subset_right
    have e1 : (Sstarv \ (⋃ x ∈ s, G.neighborSet x)).ncard
        = Sstarv.ncard - ((⋃ x ∈ s, G.neighborSet x) ∩ Sstarv).ncard := by
      have heq : Sstarv \ (⋃ x ∈ s, G.neighborSet x)
          = Sstarv \ ((⋃ x ∈ s, G.neighborSet x) ∩ Sstarv) := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_inter_iff]
        tauto
      rw [heq]
      exact Set.ncard_sdiff hsub (konig_fin _)
    have hNDsub : (⋃ x ∈ Sstarv \ (⋃ x ∈ s, G.neighborSet x), G.neighborSet x)
        ⊆ NstarU \ s := by
      intro z hz
      rw [hNmem] at hz
      obtain ⟨d, hdD, hdz⟩ := hz
      have hdS := ((Set.mem_sdiff _).mp hdD).1
      have hdN := ((Set.mem_sdiff _).mp hdD).2
      have hzN : z ∈ NstarU := (hNmem Sstarv z).mpr ⟨d, hdS, hdz⟩
      have hzs : z ∉ s := by
        intro hzs
        apply hdN
        exact Set.mem_biUnion hzs ((SimpleGraph.mem_neighborSet G z d).mpr hdz.symm)
      exact (Set.mem_sdiff _).mpr ⟨hzN, hzs⟩
    have e2 : (⋃ x ∈ Sstarv \ (⋃ x ∈ s, G.neighborSet x), G.neighborSet x).ncard
        ≤ NstarU.ncard - s.ncard := by
      have h1 := Set.ncard_le_ncard hNDsub (konig_fin _)
      have h2 : (NstarU \ s).ncard = NstarU.ncard - s.ncard :=
        Set.ncard_sdiff hs (konig_fin _)
      rwa [h2] at h1
    have hsN : s.ncard ≤ NstarU.ncard := Set.ncard_le_ncard hs (konig_fin _)
    have heq : (⋃ x ∈ s, G.neighborSet x \ Sstarvᶜ)
        = (⋃ x ∈ s, G.neighborSet x) ∩ Sstarv := by
      ext y
      simp only [Set.mem_iUnion, exists_prop, Set.mem_sdiff, Set.mem_compl_iff, not_not,
        Set.mem_inter_iff, hNmem]
      constructor
      · rintro ⟨x, hx, hxy, hyS⟩
        exact ⟨⟨x, hx, hxy⟩, hyS⟩
      · rintro ⟨⟨x, hx, hxy⟩, hyS⟩
        exact ⟨x, hx, hxy, hyS⟩
    rw [heq]
    omega
  -- Finset neighborhoods avoiding the opposite side.
  set NB : Finset V := Finset.univ.filter (· ∈ NstarU) with hNB
  have hNBcoe : ↑NB = NstarU := by
    ext x
    simp [hNB]
  set SCB : Finset V := Finset.univ.filter (· ∉ Sstarv) with hSCB
  have hSCBcoe : ↑SCB = Sstarvᶜ := by
    ext x
    simp [hSCB]
  set t1 : ↥A → Finset V := fun v => G.neighborFinset ↑v \ NB with ht1
  have ht1coe : ∀ v : ↥A, (↑(t1 v) : Set V) = G.neighborSet ↑v \ NstarU := by
    intro v
    rw [ht1, Finset.coe_sdiff, hNBcoe]
    congr 1
    rw [SimpleGraph.neighborFinset_def, Set.coe_toFinset]
  have ht1mem : ∀ v : ↥A, ∀ x : V, x ∈ t1 v → G.Adj (v : V) x ∧ x ∈ B := by
    intro v x hx
    have hx' : x ∈ G.neighborFinset ↑v \ NB := hx
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hx'
    obtain ⟨hadj, hxn⟩ := hx'
    have hvL : (v : V) ∈ L := ((Set.mem_sdiff _).mp v.property).1
    have hxR : x ∈ R := by
      rcases hmem _ _ hadj with ⟨_, hxR⟩ | ⟨hvR, _⟩
      · exact hxR
      · exact absurd hvR (Set.disjoint_left.mp hLR.disjoint hvL)
    have hxN : x ∉ NstarU := by
      rw [← hNBcoe]
      exact hxn
    exact ⟨hadj, (Set.mem_sdiff _).mpr ⟨hxR, hxN⟩⟩
  have hHall1 : ∀ c : Finset ↥A, c.card ≤ (c.biUnion t1).card :=
    konig_hall_bridge t1 ht1coe Hset1
  set t2 : ↥NstarU → Finset V := fun v => G.neighborFinset ↑v \ SCB with ht2
  have ht2coe : ∀ v : ↥NstarU, (↑(t2 v) : Set V) = G.neighborSet ↑v \ Sstarvᶜ := by
    intro v
    rw [ht2, Finset.coe_sdiff, hSCBcoe]
    congr 1
    rw [SimpleGraph.neighborFinset_def, Set.coe_toFinset]
  have ht2mem : ∀ v : ↥NstarU, ∀ x : V, x ∈ t2 v → G.Adj (v : V) x ∧ x ∈ Sstarv := by
    intro v x hx
    have hx' : x ∈ G.neighborFinset ↑v \ SCB := hx
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hx'
    obtain ⟨hadj, hxn⟩ := hx'
    have hxS : x ∈ Sstarv := by
      have h : x ∉ Sstarvᶜ := by
        rw [← hSCBcoe]
        exact hxn
      simp only [Set.mem_compl_iff, not_not] at h
      exact h
    exact ⟨hadj, hxS⟩
  have hHall2 : ∀ c : Finset ↥NstarU, c.card ≤ (c.biUnion t2).card :=
    konig_hall_bridge t2 ht2coe Hset2
  obtain ⟨M1, hM1, hc1, hs1⟩ :=
    konig_hall_match hLR.disjoint hsubAL hsubBR (fun v w h => hLR.mem_of_adj h)
      t1 ht1mem hHall1
  obtain ⟨M2, hM2, hc2, hs2⟩ :=
    konig_hall_match hLR.disjoint.symm hNR hSsL
      (fun v w h => (hLR.mem_of_adj h).elim
        (fun ⟨hvL, hwR⟩ => Or.inr ⟨hvL, hwR⟩)
        (fun ⟨hvR, hwL⟩ => Or.inl ⟨hvR, hwL⟩))
      t2 ht2mem hHall2
  have hsup1 : M1.support ⊆ A ∪ B :=
    fun x hx => hs1 (SimpleGraph.Subgraph.support_subset_verts M1 hx)
  have hsup2 : M2.support ⊆ NstarU ∪ Sstarv :=
    fun x hx => hs2 (SimpleGraph.Subgraph.support_subset_verts M2 hx)
  have hdisjAB : Disjoint (A ∪ B) (NstarU ∪ Sstarv) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_union] at hx1 hx2
    rcases hx1 with hxA | hxB <;> rcases hx2 with hxN | hxS
    · exact Set.disjoint_left.mp hLR.disjoint (hsubAL hxA) (hNR hxN)
    · exact ((Set.mem_sdiff _).mp hxA).2 hxS
    · exact ((Set.mem_sdiff _).mp hxB).2 hxN
    · exact Set.disjoint_left.mp hLR.disjoint (hSsL hxS) (hsubBR hxB)
  have hsupdisj : Disjoint M1.support M2.support :=
    Disjoint.mono hsup1 hsup2 hdisjAB
  set M : G.Subgraph := M1 ⊔ M2 with hM
  have hMmatch : M.IsMatching := hM1.sup hM2 hsupdisj
  have hedge : M.edgeSet = M1.edgeSet ∪ M2.edgeSet := SimpleGraph.Subgraph.edgeSet_sup
  have hedisj : Disjoint M1.edgeSet M2.edgeSet := by
    rw [Set.disjoint_left]
    intro e he1 he2
    obtain ⟨a, b⟩ := e
    have h1 : M1.Adj a b := SimpleGraph.Subgraph.mem_edgeSet.mp he1
    have h2 : M2.Adj a b := SimpleGraph.Subgraph.mem_edgeSet.mp he2
    have ha1 : a ∈ M1.support := (SimpleGraph.Subgraph.mem_support M1).mpr ⟨b, h1⟩
    have ha2 : a ∈ M2.support := (SimpleGraph.Subgraph.mem_support M2).mpr ⟨b, h2⟩
    exact Set.disjoint_left.mp hsupdisj ha1 ha2
  have hMcard : M.edgeSet.ncard = A.ncard + NstarU.ncard := by
    rw [hedge, Set.ncard_union_eq hedisj (konig_fin _) (konig_fin _), hc1, hc2]
  set C : Set V := A ∪ NstarU with hC
  have hCcover : G.IsVertexCover C := by
    intro v w hadj
    rcases hLR.mem_of_adj hadj with ⟨hvL, hwR⟩ | ⟨hvR, hwL⟩
    · by_cases hvS : v ∈ Sstarv
      · have hwN : w ∈ NstarU := Set.mem_biUnion hvS
          ((SimpleGraph.mem_neighborSet G v w).mpr hadj)
        change v ∈ A ∪ NstarU ∨ w ∈ A ∪ NstarU
        exact Or.inr (Or.inr hwN)
      · change v ∈ A ∪ NstarU ∨ w ∈ A ∪ NstarU
        exact Or.inl (Or.inl ((Set.mem_sdiff _).mpr ⟨hvL, hvS⟩))
    · by_cases hwS : w ∈ Sstarv
      · have hvN : v ∈ NstarU := Set.mem_biUnion hwS
          ((SimpleGraph.mem_neighborSet G w v).mpr hadj.symm)
        change v ∈ A ∪ NstarU ∨ w ∈ A ∪ NstarU
        exact Or.inl (Or.inr hvN)
      · change v ∈ A ∪ NstarU ∨ w ∈ A ∪ NstarU
        exact Or.inr (Or.inl ((Set.mem_sdiff _).mpr ⟨hwL, hwS⟩))
  have hCcard : C.ncard = A.ncard + NstarU.ncard := by
    rw [hC]
    exact Set.ncard_union_eq
      (Set.disjoint_left.mpr (fun x hxA hxN =>
        Set.disjoint_left.mp hLR.disjoint (hsubAL hxA) (hNR hxN)))
      (konig_fin _) (konig_fin _)
  exact ⟨M, C, hMmatch, hCcover, by rw [hMcard, hCcard]⟩

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/--
**Kőnig's theorem for finite bipartite graphs.** Every bipartite simple graph $G$ on a finite vertex
type $V$ has a matching $M$ and a vertex cover $C \subseteq V$ such that the number of edges of $M$
equals the number of vertices in $C$.

Proves `Wanted` entry `konig_matching_cover`.

Source: D. Kőnig (1931); J. Egerváry (1931) weighted form.
It follows from `konig_matching_cover_general`; the instances `[DecidableEq V]` and
`[DecidableRel G.Adj]` are unused and keep the source's shape.
-/
@[nolint unusedArguments]
theorem konig_matching_cover {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V),
      M.IsMatching ∧ G.IsVertexCover C ∧ M.edgeSet.ncard = C.ncard := by
  exact konig_matching_cover_general G hBip

end MathlibExt.Combinatorics.SimpleGraph.KonigMatchingCoverWanted
