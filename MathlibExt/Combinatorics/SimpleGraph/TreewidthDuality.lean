/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Bramble
public import MathlibExt.Combinatorics.SimpleGraph.TreeDecomposition
import MathlibExt.Combinatorics.SimpleGraph.Expander
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.UpperLower.Basic

/-!
# Tree-width duality

`MetaMathlibExt.hasTreewidthAtMost_iff_forall_bramble` proves the Seymour–Thomas duality
between tree-width and bramble order for finite graphs.

For the forward implication, the bags that meet a connected set form a subtree. Touching sets
give intersecting subtrees, so the clique-in-a-bag theorem supplies one bag meeting every member
of the bramble.

For the converse we use Mazoit's partial decomposition argument. We represent a partial
decomposition recursively by its unresolved regions and small bags. Minimizing the size of an
external boundary allows two partial decompositions to be glued across a separator.

## References

* Frédéric Mazoit, *A simple proof of the tree-width duality theorem*,
  https://arxiv.org/abs/1309.2266.
-/

namespace MetaMathlibExt

open SimpleGraph

namespace TreewidthDuality

open Set

universe u

variable {V : Type u} {G : SimpleGraph V}

section BrambleCover

variable (D : G.TreeDecomposition)

private theorem walk_meeting_of_mem {X : Set V} {v : V} (hv : v ∈ X)
    {s t : D.ι} (hs : v ∈ D.bag s) (ht : v ∈ D.bag t) :
    ∃ p : D.T.Walk s t, ∀ i ∈ p.support, (D.bag i ∩ X).Nonempty := by
  obtain ⟨p, hp⟩ := (D.isTree.existsUnique_path s t).exists
  exact ⟨p, fun i hi => ⟨v, D.coherent s t i p hp hi ⟨hs, ht⟩, hv⟩⟩

private theorem lift_walk {X : Set V} {x y : X} (w : (G.induce X).Walk x y)
    {s t : D.ι} (hs : x.val ∈ D.bag s) (ht : y.val ∈ D.bag t) :
    ∃ p : D.T.Walk s t, ∀ i ∈ p.support, (D.bag i ∩ X).Nonempty := by
  induction w generalizing s with
  | @nil u => exact walk_meeting_of_mem D u.property hs ht
  | @cons u v _ huv w ih =>
    obtain ⟨j, hu, hv⟩ := D.edge_mem u.val v.val huv
    obtain ⟨p, hp⟩ := walk_meeting_of_mem D u.property hs hu
    obtain ⟨q, hq⟩ := ih hv ht
    refine ⟨p.append q, fun i hi => ?_⟩
    rcases (Walk.mem_support_append_iff p q).mp hi with h | h
    · exact hp i h
    · exact hq i h

private theorem meets_on_path {X : Set V} (hX : (G.induce X).Connected)
    {s t i : D.ι} (hs : (D.bag s ∩ X).Nonempty) (ht : (D.bag t ∩ X).Nonempty)
    (p : D.T.Walk s t) (hp : p.IsPath) (hi : i ∈ p.support) :
    (D.bag i ∩ X).Nonempty := by
  classical
  obtain ⟨x, hxs, hx⟩ := hs
  obtain ⟨y, hyt, hy⟩ := ht
  obtain ⟨w⟩ := hX.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨q, hq⟩ := lift_walk D w hxs hyt
  have he := D.isTree.isAcyclic.subsingleton_path s t |>.elim ⟨p, hp⟩ q.toPath
  have heq : p = q.toPath.val := congrArg Subtype.val he
  exact hq _ (q.support_toPath_subset_support (heq ▸ hi))

private theorem exists_bag_cover {B : Set (Set V)} (hB : G.IsBramble B) [Finite V] :
    ∃ i, ∀ X ∈ B, (D.bag i ∩ X).Nonempty := by
  classical
  let E : (⊤ : SimpleGraph B).TreeDecomposition := {
    ι := D.ι
    finite := D.finite
    T := D.T
    isTree := D.isTree
    bag := fun t => {X | (D.bag t ∩ X.val).Nonempty}
    cover := by
      intro X
      obtain ⟨⟨x, hx⟩⟩ := (hB.1 _ X.property).nonempty
      obtain ⟨t, ht⟩ := D.cover x
      exact ⟨t, x, ht, hx⟩
    edge_mem := by
      intro X Y _
      rcases hB.2 _ X.property _ Y.property with ⟨z, hx, hy⟩ | ⟨x, hx, y, hy, hxy⟩
      · obtain ⟨t, ht⟩ := D.cover z
        exact ⟨t, ⟨z, ht, hx⟩, z, ht, hy⟩
      · obtain ⟨t, hxt, hyt⟩ := D.edge_mem x y hxy
        exact ⟨t, ⟨x, hxt, hx⟩, y, hyt, hy⟩
    coherent := fun _ _ _ p hp hi X ⟨hs, ht⟩ =>
      meets_on_path D (hB.1 _ X.property) hs ht p hp hi }
  let := Fintype.ofFinite B
  obtain ⟨i, hi⟩ := E.exists_bag_superset Finset.univ (by simp)
  exact ⟨i, fun X hX => hi (show (⟨X, hX⟩ : B) ∈ Finset.univ from Finset.mem_univ _)⟩

private theorem no_large_bramble [Finite V] {k : ℕ} (h : G.HasTreewidthAtMost k) :
    ∀ (B : Set (Set V)) (hB : G.IsBramble B), ¬hB.OrderGT (k + 1) := by
  classical
  obtain ⟨D, hD⟩ := h
  intro B hB hGT
  obtain ⟨i, hi⟩ := exists_bag_cover D hB
  let S := (D.bag i).toFinite.toFinset
  have hS : S.card ≤ k + 1 := by
    have := hD i
    rw [(D.bag i).toFinite.encard_eq_coe_toFinset_card] at this
    exact_mod_cast this
  obtain ⟨X, hX, hd⟩ := hGT S hS
  obtain ⟨v, hv, hvX⟩ := hi X hX
  exact hd v hvX (by simpa [S] using hv)

end BrambleCover

variable {A B C D X Y Z : Set V}

-- A region consists of the vertices still to decompose. Its external neighbours must
-- remain in its root bag so that the region can be attached to the rest of the graph.
private def closedNeighborhood (G : SimpleGraph V) (A : Set V) : Set V :=
  {x | x ∈ A ∨ ∃ a ∈ A, G.Adj x a}

private def exterior (G : SimpleGraph V) (A : Set V) := (closedNeighborhood G A)ᶜ

private theorem mem_closedNeighborhood {x : V} :
    x ∈ closedNeighborhood G A ↔ x ∈ A ∨ ∃ a ∈ A, G.Adj x a := Iff.rfl

private theorem externalNeighborSet_eq :
    G.externalNeighborSet A = closedNeighborhood G A \ A := by
  ext x
  simp only [mem_externalNeighborSet, mem_sdiff, mem_closedNeighborhood]
  grind [SimpleGraph.adj_comm]

private theorem closedNeighborhood_mono (h : A ⊆ B) :
    closedNeighborhood G A ⊆ closedNeighborhood G B := by
  simp only [Set.subset_def, mem_closedNeighborhood] at *
  grind

private theorem subset_closedNeighborhood : A ⊆ closedNeighborhood G A := fun _ h => Or.inl h

private theorem exterior_anti (h : A ⊆ B) : exterior G B ⊆ exterior G A :=
  compl_subset_compl.mpr (closedNeighborhood_mono h)

private theorem exterior_comm : A ⊆ exterior G B ↔ B ⊆ exterior G A := by
  simp only [Set.subset_def, exterior, mem_compl_iff, mem_closedNeighborhood]
  grind [SimpleGraph.adj_comm]

private theorem exterior_iff : A ⊆ exterior G B ↔ ¬ G.Touch A B := by
  simp only [Set.subset_def, exterior, mem_compl_iff, mem_closedNeighborhood, SimpleGraph.Touch,
    Set.nonempty_def, mem_inter_iff]
  grind

private theorem subset_exterior_exterior : A ⊆ exterior G (exterior G A) :=
  exterior_comm.mpr Subset.rfl

private theorem boundary_exterior_subset :
    G.externalNeighborSet (exterior G A) ⊆ G.externalNeighborSet A := by
  rw [externalNeighborSet_eq, externalNeighborSet_eq]
  intro x ⟨hx, hn⟩
  exact ⟨not_not.mp hn, fun hxA => subset_exterior_exterior hxA hx⟩

private def Separated (G : SimpleGraph V) (K : Set (Set V)) :=
  ∀ C ∈ K, ∀ D ∈ K, C ≠ D → C ⊆ exterior G D

/-- A partial decomposition of a region may leave any member of `L` as an unresolved leaf.
At a junction, the children are mutually non-touching subsets of the region. Their complement
in its closed neighbourhood is the bag at that junction. -/
private inductive Decomposable (G : SimpleGraph V) (n : ℕ) (L : Set (Set V)) : Set V → Prop
  | leaf {A : Set V} (hA : A ∈ L) : Decomposable G n L A
  | join {A : Set V} (K : Set (Set V)) (sub : ⋃₀ K ⊆ A) (sep : Separated G K)
      (small : (closedNeighborhood G A \ ⋃₀ K).ncard ≤ n)
      (below : ∀ C ∈ K, Decomposable G n L C) : Decomposable G n L A

private theorem boundary_child_subset_bag {K : Set (Set V)} (hs : ⋃₀ K ⊆ A) (hK : Separated G K)
    (hc : C ∈ K) : G.externalNeighborSet C ⊆ closedNeighborhood G A \ ⋃₀ K := by
  rw [externalNeighborSet_eq]
  rintro x ⟨hx, hn⟩
  refine ⟨closedNeighborhood_mono ((subset_sUnion_of_mem hc).trans hs) hx, ?_⟩
  rintro ⟨D, hd, hxd⟩
  by_cases he : D = C
  · exact hn (he ▸ hxd)
  · exact hK D hd C hc he hxd hx

private theorem decomposable_empty {n L} : Decomposable G n L ∅ := by
  apply Decomposable.join ∅ <;> simp [closedNeighborhood, Separated]

/-- Restrict a junction to a side `Z` of minimum boundary. Write `U` for the union of the
children. Each boundary vertex in `U` can enter the new bag. Minimality for `Z ∪ U` bounds
their number by the number of old bag vertices outside the closed neighbourhood of `Z`. -/
private theorem bag_ncard_inter_le [Finite V] {K : Set (Set V)}
    (hs : ⋃₀ K ⊆ D)
    (hmin : (G.externalNeighborSet Z).ncard ≤ (G.externalNeighborSet (Z ∪ ⋃₀ K)).ncard) :
    (closedNeighborhood G (D ∩ Z) \ (⋃₀ K ∩ Z)).ncard ≤ (closedNeighborhood G D \ ⋃₀ K).ncard := by
  classical
  let U := ⋃₀ K
  let S := G.externalNeighborSet Z
  let Q := closedNeighborhood G D \ U
  have h1 : G.externalNeighborSet (Z ∪ U) ⊆ (S \ U) ∪ (Q \ closedNeighborhood G Z) := by
    rw [externalNeighborSet_eq]
    intro x ⟨hx, hn⟩
    have hzx : x ∉ Z := fun h => hn (Or.inl h)
    have hux : x ∉ U := fun h => hn (Or.inr h)
    by_cases h : x ∈ closedNeighborhood G Z
    · have hS : x ∈ S := by
        change x ∈ G.externalNeighborSet Z
        rw [externalNeighborSet_eq]
        exact ⟨h, hzx⟩
      exact Or.inl ⟨hS, hux⟩
    · refine Or.inr ⟨⟨?_, hux⟩, h⟩
      rcases hx with hx | ⟨a, ha | ha, hxa⟩
      · exact (hn hx).elim
      · exact (h (Or.inr ⟨a, ha, hxa⟩)).elim
      · exact Or.inr ⟨a, hs ha, hxa⟩
  have h2 : (S ∩ U).ncard ≤ (Q \ closedNeighborhood G Z).ncard := by
    have h := hmin.trans ((Set.ncard_le_ncard h1).trans (Set.ncard_union_le ..))
    have hspl := Set.ncard_inter_add_ncard_sdiff_eq_ncard S U
    change S.ncard ≤ (S \ U).ncard + (Q \ closedNeighborhood G Z).ncard at h
    omega
  have h3 : closedNeighborhood G (D ∩ Z) \ (U ∩ Z) ⊆ (Q ∩ closedNeighborhood G Z) ∪ (S ∩ U) := by
    rintro x ⟨hx, hn⟩
    have hz := closedNeighborhood_mono (G := G) (inter_subset_right : D ∩ Z ⊆ Z) hx
    by_cases hu : x ∈ U
    · have hS : x ∈ S := by
        change x ∈ G.externalNeighborSet Z
        rw [externalNeighborSet_eq]
        exact ⟨hz, fun h => hn ⟨hu, h⟩⟩
      exact Or.inr ⟨hS, hu⟩
    · exact Or.inl ⟨⟨closedNeighborhood_mono inter_subset_left hx, hu⟩, hz⟩
  have h4 := (Set.ncard_le_ncard h3).trans (Set.ncard_union_le ..)
  have h5 := Set.ncard_inter_add_ncard_sdiff_eq_ncard Q (closedNeighborhood G Z)
  change (closedNeighborhood G (D ∩ Z) \ (U ∩ Z)).ncard ≤ Q.ncard
  omega

private theorem decomposable_inter [Finite V] {n L} (hL : IsLowerSet L)
    (h : Decomposable G n L D) (hDA : D ⊆ A)
    (hmin : ∀ U ⊆ A, (G.externalNeighborSet Z).ncard ≤ (G.externalNeighborSet (Z ∪ U)).ncard) :
    Decomposable G n L (D ∩ Z) := by
  induction h with
  | leaf h => exact .leaf (hL inter_subset_left h)
  | @join D K sub sep small _ ih =>
    let K' := (fun C : Set V => C ∩ Z) '' K
    have he : ⋃₀ K' = ⋃₀ K ∩ Z := by ext; simp [K']; grind
    apply Decomposable.join K'
    · rw [he]; exact inter_subset_inter_left Z sub
    · rintro _ ⟨C, hc, rfl⟩ _ ⟨E, he', rfl⟩ hne
      exact (inter_subset_left.trans (sep _ hc _ he' (fun h => hne (h ▸ rfl)))).trans
        (exterior_anti inter_subset_left)
    · rw [he]
      exact (bag_ncard_inter_le sub (hmin _ (sub.trans hDA))).trans small
    · rintro _ ⟨C, hc, rfl⟩
      exact ih C hc ((subset_sUnion_of_mem hc).trans (sub.trans hDA))

/-- Viewed from a child, the other children and the old exterior form the new branches.
The new junction bag is contained in the old one. -/
private theorem reroot_child [Finite V] {K : Set (Set V)} {n L}
    (hs : ⋃₀ K ⊆ A) (hK : Separated G K) (hc : C ∈ K)
    (hsize : (closedNeighborhood G A \ ⋃₀ K).ncard ≤ n) (hout : Decomposable G n L (exterior G A))
    (hbro : ∀ E ∈ K, E ≠ C → Decomposable G n L E) : Decomposable G n L (exterior G C) := by
  classical
  let K' := insert (exterior G A) (K \ {C})
  have hmem {E : Set V} : E ∈ K' ↔ E = exterior G A ∨ E ∈ K ∧ E ≠ C := Iff.rfl
  have hsub {E : Set V} (hE : E ∈ K) : E ⊆ A := (subset_sUnion_of_mem hE).trans hs
  have hsep {E : Set V} (hE : E ∈ K) : exterior G A ⊆ exterior G E :=
    exterior_anti (hsub hE)
  apply Decomposable.join K'
  · rintro x ⟨E, hE, hx⟩
    rcases hmem.mp hE with rfl | ⟨he, hn⟩
    · exact hsep hc hx
    · exact hK _ he _ hc hn hx
  · intro E he F hf hn
    rcases hmem.mp he with rfl | ⟨he, -⟩ <;> rcases hmem.mp hf with rfl | ⟨hf, -⟩
    · exact (hn rfl).elim
    · exact exterior_comm.mpr ((hsub hf).trans subset_exterior_exterior)
    · exact (hsub he).trans subset_exterior_exterior
    · exact hK _ he _ hf hn
  · apply le_trans (Set.ncard_le_ncard _) hsize
    rintro x ⟨hx, hn⟩
    constructor
    · by_contra h
      exact hn ⟨_, hmem.mpr (Or.inl rfl), h⟩
    · rintro ⟨E, he, hxe⟩
      by_cases h : E = C
      · exact subset_exterior_exterior (h ▸ hxe) hx
      · exact hn ⟨_, hmem.mpr (Or.inr ⟨he, h⟩), hxe⟩
  · intro E he
    rcases hmem.mp he with rfl | ⟨he, hn⟩
    · exact hout
    · exact hbro _ he hn

/-- Follow an unresolved leaf `X` and decompose its exterior. The leaf is nonempty, so at most
one child can contain it and all its siblings can be decomposed using only `L`. -/
private theorem reroot [Finite V] {n L} (hX : X.Nonempty)
    (h : Decomposable G n (insert X L) A) :
    Decomposable G n L A ∨ X ⊆ A ∧
      (Decomposable G n L (exterior G A) → (G.externalNeighborSet A).ncard ≤ n →
        Decomposable G n L (exterior G X) ∧ (G.externalNeighborSet X).ncard ≤ n) := by
  classical
  induction h with
  | leaf h =>
    rcases h with he | h
    · subst he
      exact Or.inr ⟨Subset.rfl, fun h h' => ⟨h, h'⟩⟩
    · exact Or.inl (.leaf h)
  | @join A K hs sep small below ih =>
    by_cases hall : ∀ C ∈ K, Decomposable G n L C
    · exact Or.inl (.join K hs sep small hall)
    push Not at hall
    obtain ⟨C, hc, hn⟩ := hall
    obtain ⟨hxc, hrec⟩ := (ih C hc).resolve_left hn
    refine Or.inr ⟨hxc.trans ((subset_sUnion_of_mem hc).trans hs), fun hout _ => hrec ?_ ?_⟩
    · apply reroot_child hs sep hc small hout
      intro E he hne
      rcases ih E he with h | ⟨heX, -⟩
      · exact h
      · obtain ⟨x, hx⟩ := hX
        exact (sep E he C hc hne (heX hx) (subset_closedNeighborhood (hxc hx))).elim
    · exact (Set.ncard_le_ncard (boundary_child_subset_bag hs sep hc)).trans small

/-- Glue decompositions of the exteriors of two non-touching leaves. Choose a side containing
`Y` and avoiding the closed neighbourhood of `X` with smallest boundary. Both exteriors can
be restricted to the corresponding sides without increasing bag sizes. -/
private theorem decomposable_univ_of_separated [Finite V] {n L} (hL : IsLowerSet L)
    (hxy : X ⊆ exterior G Y) (hx : Decomposable G n L (exterior G X))
    (hy : Decomposable G n L (exterior G Y)) (hxb : (G.externalNeighborSet X).ncard ≤ n) :
    Decomposable G n L univ := by
  classical
  let ok := {Z : Set V | Y ⊆ Z ∧ Z ⊆ exterior G X}
  have hne : ok.Nonempty := ⟨exterior G X, exterior_comm.mp hxy, Subset.rfl⟩
  let Z := Function.argminOn (fun Z => (G.externalNeighborSet Z).ncard) ok hne
  have hz : Z ∈ ok := Function.argminOn_mem _ _ _
  have hm (U) (hU : U ∈ ok) : (G.externalNeighborSet Z).ncard ≤ (G.externalNeighborSet U).ncard :=
    Function.argminOn_le (f := fun U => (G.externalNeighborSet U).ncard) ok hU
  let W := exterior G Z
  have hw : W ⊆ exterior G Y := exterior_anti hz.1
  have hxW : X ⊆ W := exterior_comm.mp hz.2
  have hZ : Decomposable G n L Z := by
    rw [← inter_eq_right.mpr hz.2]
    apply decomposable_inter hL hx Subset.rfl
    exact fun U hU => hm _ ⟨hz.1.trans subset_union_left, union_subset hz.2 hU⟩
  have hW : Decomposable G n L W := by
    rw [← inter_eq_right.mpr hw]
    apply decomposable_inter hL hy Subset.rfl
    intro U hU
    have hwu : W ∪ U ⊆ exterior G Y := union_subset hw hU
    have he : exterior G (W ∪ U) ∈ ok :=
      ⟨exterior_comm.mp hwu, exterior_anti (hxW.trans subset_union_left)⟩
    calc
      _ ≤ (G.externalNeighborSet Z).ncard := Set.ncard_le_ncard boundary_exterior_subset
      _ ≤ _ := hm _ he
      _ ≤ _ := Set.ncard_le_ncard boundary_exterior_subset
  apply Decomposable.join {Z, W} (subset_univ _)
  · intro E he F hf hn
    rcases he with rfl | he <;> rcases hf with rfl | hf
    · exact (hn rfl).elim
    · rw [mem_singleton_iff.mp hf]
      exact subset_exterior_exterior
    · rw [mem_singleton_iff.mp he]
    · exact (hn ((mem_singleton_iff.mp he).trans (mem_singleton_iff.mp hf).symm)).elim
  · have h : closedNeighborhood G univ \ ⋃₀ {Z, W} ⊆ G.externalNeighborSet Z := by
      rw [externalNeighborSet_eq]
      intro x hx
      have hn : x ∉ Z ∧ x ∉ W := by simpa using hx.2
      exact ⟨not_not.mp hn.2, hn.1⟩
    have he : exterior G X ∈ ok := ⟨exterior_comm.mp hxy, Subset.rfl⟩
    calc
      _ ≤ _ := Set.ncard_le_ncard h
      _ ≤ _ := hm _ he
      _ ≤ _ := Set.ncard_le_ncard boundary_exterior_subset
      _ ≤ n := hxb
  · intro E he
    rcases he with rfl | he
    · exact hZ
    · exact mem_singleton_iff.mp he ▸ hW

/-- If a small set met every connected region outside `L`, the components of its complement
would form the leaves of a partial decomposition with that set as root bag. -/
private theorem exists_connected_outside [Finite V] {n L} (hn : ¬Decomposable G n L univ)
    (S : Finset V) (hS : S.card ≤ n) :
    ∃ C ∉ L, (G.induce C).Connected ∧ ∀ x ∈ C, x ∉ S := by
  classical
  let T := (S : Set V)ᶜ
  let H := G.induce T
  let part := fun c : H.ConnectedComponent => Subtype.val '' c.supp
  have hsep : Separated G (range part) := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ hn x ⟨u, hu, rfl⟩ hx
    apply hn
    congr 1
    apply ConnectedComponent.eq_of_common_vertex (v := u) hu
    rcases hx with ⟨v, hv, he⟩ | ⟨_, ⟨v, hv, rfl⟩, hvu⟩
    · exact Subtype.ext he ▸ hv
    · exact d.mem_supp_of_adj_mem_supp hv (G.adj_symm hvu)
  have hc : ∃ c, part c ∉ L := by
    by_contra! hall
    apply hn
    apply Decomposable.join (range part) (subset_univ _) hsep
    · apply le_trans (Set.ncard_le_ncard (t := (↑S : Set V)) _) (by simpa using hS)
      rintro x ⟨-, hx⟩
      by_contra h
      let v : T := ⟨x, h⟩
      exact hx ⟨_, ⟨H.connectedComponentMk v, rfl⟩, v, rfl, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact .leaf (hall c)
  obtain ⟨c, h⟩ := hc
  refine ⟨part c, h, ?_, ?_⟩
  · let f : c.toSimpleGraph →g G.induce (part c) :=
      ⟨fun x => ⟨x.val.val, x.val, x.property, rfl⟩, fun h => h⟩
    apply c.connected_toSimpleGraph.map f
    rintro ⟨_, v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact v.property

/-- Choose a maximal downward-closed family of allowed leaves for which the whole graph
cannot be decomposed. Two minimal excluded leaves must touch, since otherwise their exterior
decompositions could be glued. The connected excluded regions then form a bramble. -/
private theorem decomposable_of_bramble_bound [Finite V] {n : ℕ}
    (hcover : ∀ (B : Set (Set V)) (h : G.IsBramble B), ¬h.OrderGT n) :
    Decomposable G n ∅ univ := by
  classical
  by_contra hn
  let families := {L : Set (Set V) | IsLowerSet L ∧ ¬Decomposable G n L univ}
  have hne : families.Nonempty := ⟨∅, isLowerSet_empty, hn⟩
  obtain ⟨L, hL, hmax⟩ := families.toFinite.exists_maximal hne
  have down : IsLowerSet L := hL.1
  have fail : ¬Decomposable G n L univ := hL.2
  have solve {X : Set V} (hm : Minimal (· ∉ L) X) :
      Decomposable G n L (exterior G X) ∧ (G.externalNeighborSet X).ncard ≤ n := by
    have d' : IsLowerSet (insert X L) := by
      intro F E hs hf
      rcases hf with rfl | hf
      · by_cases hE : E ∈ L
        · exact Or.inr hE
        · exact Or.inl (Subset.antisymm hs (hm.2 hE hs))
      · exact Or.inr (down hs hf)
    have h' : Decomposable G n (insert X L) univ := by
      by_contra hf
      have := hmax (show insert X L ∈ families from ⟨d', hf⟩) (subset_insert X L)
      exact hm.1 (this (mem_insert _ _))
    have hx : X.Nonempty := by
      by_contra! he
      subst X
      have hl {A} (h : Decomposable G n (insert ∅ L) A) : Decomposable G n L A := by
        induction h with
        | leaf h =>
          rcases h with rfl | h
          · exact decomposable_empty
          · exact .leaf h
        | join K sub sep small _ ih => exact .join K sub sep small ih
      exact fail (hl h')
    have h := ((reroot hx h').resolve_left fail).2
    apply h <;> simp [exterior, externalNeighborSet_eq, closedNeighborhood, decomposable_empty]
  let B := {C : Set V | C ∉ L ∧ (G.induce C).Connected}
  have br : G.IsBramble B := by
    refine ⟨fun C h => h.2, ?_⟩
    intro C hc D hd
    by_contra h
    obtain ⟨X, hxC, hX⟩ := Lᶜ.toFinite.exists_le_minimal hc.1
    obtain ⟨Y, hyD, hY⟩ := Lᶜ.toFinite.exists_le_minimal hd.1
    have hxy := hxC.trans ((exterior_iff.mpr h).trans (exterior_anti hyD))
    exact fail (decomposable_univ_of_separated down hxy (solve hX).1 (solve hY).1 (solve hX).2)
  apply hcover B br
  intro S hS
  obtain ⟨C, h, hc, hd⟩ := exists_connected_outside fail S hS
  exact ⟨C, ⟨h, hc⟩, hd⟩

-- Realize a recursive decomposition as a finite rooted tree. Parent links decrease depth,
-- and for each vertex the bags containing it have a common highest occurrence.
private structure ParentTree where
  Node : Type u
  [finite : Finite Node]
  root : Node
  parent : Node → Node
  depth : Node → ℕ
  fixed : parent root = root
  down : ∀ t, t ≠ root → depth (parent t) < depth t

attribute [local instance] ParentTree.finite

private def ParentTree.graph (F : ParentTree) : SimpleGraph F.Node :=
  fromRel (fun t s => F.parent t = s)

private theorem ParentTree.adj_parent (F : ParentTree) {t : F.Node} (ht : t ≠ F.root) :
    F.graph.Adj t (F.parent t) :=
  ⟨fun h => (F.down _ ht).ne (congrArg F.depth h.symm), Or.inl rfl⟩

private theorem ParentTree.isTree (F : ParentTree) : F.graph.IsTree := by
  classical
  let rec reach (t : F.Node) : F.graph.Reachable t F.root := by
    by_cases ht : t = F.root
    · subst t; exact .rfl
    · exact (F.adj_parent ht).reachable.trans (reach (F.parent t))
  termination_by F.depth t
  decreasing_by exact F.down _ ht
  have conn : F.graph.Connected := (connected_iff_exists_forall_reachable ..).mpr
    ⟨F.root, fun t => (reach t).symm⟩
  apply isTree_iff_connected_and_card.mpr
  refine ⟨conn, le_antisymm ?_ conn.card_vert_le_card_edgeSet_add_one⟩
  let U := ({F.root} : Set F.Node)ᶜ
  have sub : F.graph.edgeSet ⊆ (fun t => s(t, F.parent t)) '' U := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      change F.graph.Adj u v → _
      rintro ⟨hne, h | h⟩
      · refine ⟨u, fun (h' : u = F.root) => hne (by simpa [h', F.fixed] using h), ?_⟩
        exact congrArg (fun w => s(u, w)) h
      · exact ⟨v, fun (h' : v = F.root) => hne.symm (by simpa [h', F.fixed] using h),
          (congrArg (fun w => s(v, w)) h).trans (Sym2.eq_swap ..)⟩
  have hc := (Set.ncard_le_ncard sub).trans (Set.ncard_image_le ..)
  have hu := Set.ncard_add_ncard_compl ({F.root} : Set F.Node)
  simp only [Set.ncard_singleton] at hu
  change F.graph.edgeSet.ncard + 1 ≤ _
  change F.graph.edgeSet.ncard ≤ ({F.root} : Set F.Node)ᶜ.ncard at hc
  omega

private theorem ParentTree.coherent {α : Type*} (F : ParentTree) (bag : F.Node → Set α)
    (occ : ∀ v, ∃ t, ∀ s, v ∈ bag s → s ≠ t → s ≠ F.root ∧ v ∈ bag (F.parent s))
    (s t i : F.Node) (p : F.graph.Walk s t) (hp : p.IsPath) (hi : i ∈ p.support) :
    bag s ∩ bag t ⊆ bag i := by
  classical
  rintro v ⟨hs, ht⟩
  obtain ⟨top, htop⟩ := occ v
  let rec ascend (x : F.Node) (hx : v ∈ bag x) :
      ∃ q : F.graph.Walk x top, ∀ j ∈ q.support, v ∈ bag j := by
    by_cases he : x = top
    · subst x; exact ⟨.nil, by simpa using hx⟩
    · obtain ⟨hn, hpar⟩ := htop x hx he
      obtain ⟨q, hq⟩ := ascend (F.parent x) hpar
      exact ⟨.cons (F.adj_parent hn) q, by simpa [hx] using hq⟩
  termination_by F.depth x
  decreasing_by exact F.down _ hn
  obtain ⟨q, hq⟩ := ascend s hs
  obtain ⟨r, hr⟩ := ascend t ht
  let w := q.append r.reverse
  have he : p = w.toPath.val := congrArg Subtype.val <|
    F.isTree.isAcyclic.subsingleton_path s t |>.elim ⟨p, hp⟩ w.toPath
  have hw := w.support_toPath_subset_support (he ▸ hi)
  rcases (Walk.mem_support_append_iff ..).mp hw with h | h
  · exact hq i h
  · exact hr i (by simpa using h)

private noncomputable def branches {I : Type u} [Finite I] (F : I → ParentTree.{u}) :
    ParentTree.{u} := by
  classical
  let N := Option (Σ i, (F i).Node)
  let par : N → N
    | none => none
    | some ⟨i, t⟩ => if t = (F i).root then none else some ⟨i, (F i).parent t⟩
  let depth : N → ℕ
    | none => 0
    | some ⟨i, t⟩ => (F i).depth t + 1
  refine ⟨N, none, par, depth, rfl, ?_⟩
  rintro (_ | ⟨i, t⟩) hn
  · trivial
  · by_cases h : t = (F i).root
    · simp [par, depth, h]
    · simpa [par, depth, h] using (F i).down t h

/-- A rooted decomposition of a region, with its entire external boundary in the root bag.
For every vertex, all occurrences ascend through bags containing it to a common node. -/
private structure RegionDecomposition {V : Type u} (G : SimpleGraph V) (n : ℕ) (A : Set V) where
  tree : ParentTree.{u}
  bag : tree.Node → Set V
  inside : ∀ t, bag t ⊆ closedNeighborhood G A
  attach : G.externalNeighborSet A ⊆ bag tree.root
  size : ∀ t, (bag t).ncard ≤ n
  cover : ∀ x ∈ A, ∃ t, x ∈ bag t
  edge : ∀ x ∈ A, ∀ y, G.Adj x y → ∃ t, x ∈ bag t ∧ y ∈ bag t
  occ : ∀ v, ∃ t, ∀ s, v ∈ bag s → s ≠ t → s ≠ tree.root ∧ v ∈ bag (tree.parent s)

/-- Assemble the child trees under the junction bag. A vertex in the junction bag appears in
a child only through its boundary. Every other vertex occurs in at most one child. -/
private theorem regionDecomposition_of_decomposable [Finite V] {n} (h : Decomposable G n ∅ A) :
    Nonempty (RegionDecomposition G n A) := by
  classical
  induction h with
  | leaf h => exact h.elim
  | @join A K sub sep small _ ih =>
    let P (c : K) := (ih c.val c.property).some
    let F := branches fun c => (P c).tree
    let R := closedNeighborhood G A \ ⋃₀ K
    let bag : F.Node → Set V
      | none => R
      | some ⟨c, t⟩ => (P c).bag t
    have hsub (c : K) : (c.val : Set V) ⊆ A := (subset_sUnion_of_mem c.property).trans sub
    have shared (c : K) : G.externalNeighborSet c.val ⊆ R :=
      boundary_child_subset_bag sub sep c.property
    have arrive (x : V) (c : K) (t : (P c).tree.Node) (ht : x ∈ (P c).bag t) :
        x ∈ c.val ∨ x ∈ R := by
      by_cases hc : x ∈ c.val
      · exact Or.inl hc
      · exact Or.inr (shared c (externalNeighborSet_eq.symm ▸ ⟨(P c).inside t ht, hc⟩))
    refine ⟨⟨F, bag, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rintro (_ | ⟨c, t⟩)
      · exact sdiff_subset
      · exact ((P c).inside t).trans (closedNeighborhood_mono (hsub c))
    · rw [externalNeighborSet_eq]
      exact fun _ hx => ⟨hx.1, fun h => hx.2 (sub h)⟩
    · rintro (_ | ⟨c, t⟩)
      · exact small
      · exact (P c).size t
    · intro x hx
      by_cases h : x ∈ ⋃₀ K
      · obtain ⟨C, hC, hxC⟩ := h
        let c : K := ⟨C, hC⟩
        obtain ⟨t, ht⟩ := (P c).cover x hxC
        exact ⟨some ⟨c, t⟩, ht⟩
      · exact ⟨none, subset_closedNeighborhood hx, h⟩
    · intro x hx y hxy
      have liftEdge (x y : V) (h : x ∈ ⋃₀ K) (he : G.Adj x y) :
          ∃ t, x ∈ bag t ∧ y ∈ bag t := by
        obtain ⟨C, hC, hxC⟩ := h
        let c : K := ⟨C, hC⟩
        obtain ⟨t, ht⟩ := (P c).edge x hxC y he
        exact ⟨some ⟨c, t⟩, ht⟩
      by_cases h : x ∈ ⋃₀ K
      · exact liftEdge x y h hxy
      by_cases h' : y ∈ ⋃₀ K
      · obtain ⟨t, ht⟩ := liftEdge y x h' hxy.symm
        exact ⟨t, ht.2, ht.1⟩
      exact ⟨none, ⟨subset_closedNeighborhood hx, h⟩, Or.inr ⟨x, hx, hxy.symm⟩, h'⟩
    · intro v
      by_cases hv : v ∈ R
      · refine ⟨none, ?_⟩
        rintro (_ | ⟨c, s⟩) hs hn
        · exact (hn rfl).elim
        · refine ⟨Option.some_ne_none _, ?_⟩
          by_cases he : s = (P c).tree.root
          · simpa [F, branches, he, bag] using hv
          · obtain ⟨t, ht⟩ := (P c).occ v
            have hroot : v ∈ (P c).bag (P c).tree.root :=
              (P c).attach (externalNeighborSet_eq.symm ▸
                ⟨(P c).inside s hs, fun h => hv.2 (subset_sUnion_of_mem c.property h)⟩)
            have heq : (P c).tree.root = t := by
              by_contra hn
              exact (ht _ hroot hn).1 rfl
            have hpar := (ht s hs (heq ▸ he)).2
            simpa [F, branches, he, bag] using hpar
      · by_cases hex : ∃ c : K, v ∈ c.val
        · obtain ⟨c, hc⟩ := hex
          obtain ⟨t, ht⟩ := (P c).occ v
          refine ⟨some ⟨c, t⟩, ?_⟩
          rintro (_ | ⟨d, s⟩) hs hn
          · exact (hv hs).elim
          · have hd := (arrive _ d s hs).resolve_right hv
            have hdc : d = c := by
              by_contra h
              exact sep _ d.property _ c.property (fun he => h (Subtype.ext he)) hd
                (subset_closedNeighborhood hc)
            subst d
            have hst : s ≠ t := fun he => hn (he ▸ rfl)
            obtain ⟨he, hpar⟩ := ht s hs hst
            exact ⟨Option.some_ne_none _, by simpa [F, branches, he, bag] using hpar⟩
        · refine ⟨none, ?_⟩
          rintro (_ | ⟨c, s⟩) hs hn
          · exact (hv hs).elim
          · exact (hex ⟨c, (arrive _ c s hs).resolve_right hv⟩).elim

private theorem width_of_decomposable [Finite V] {k : ℕ} (h : Decomposable G (k + 1) ∅ univ) :
    G.HasTreewidthAtMost k := by
  classical
  obtain ⟨P⟩ := regionDecomposition_of_decomposable h
  refine ⟨{ ι := P.tree.Node, T := P.tree.graph, isTree := P.tree.isTree, bag := P.bag,
            cover := fun x => P.cover x trivial, edge_mem := fun x => P.edge x trivial,
            coherent := P.tree.coherent _ P.occ }, ?_⟩
  intro t
  change (P.bag t).encard ≤ _
  rw [← Set.coe_ncard_eq_encard]
  exact_mod_cast P.size t

end TreewidthDuality

/-- **Tree-width duality theorem (Seymour–Thomas).** For every finite graph `G` and every
`k : ℕ`, `G` has tree-width at most `k` if and only if it contains no bramble of order greater
than `k + 1` (Diestel, *Graph Theory*, 6th ed., Theorem 12.4.3, "a graph has tree-width `< k` if
and only if it contains no bramble of order `> k`", applied with `k + 1`; P. D. Seymour and
R. Thomas, *Graph searching and a min-max theorem for tree-width*, J. Combin. Theory Ser. B 58
(1993) 22–33). The source's case `k = 0`, which concerns only the graph with no vertices, is not
part of this statement. -/
public theorem hasTreewidthAtMost_iff_forall_bramble {V : Type*} [Finite V] (G : SimpleGraph V)
    (k : ℕ) :
    G.HasTreewidthAtMost k ↔ ∀ (B : Set (Set V)) (hB : G.IsBramble B), ¬hB.OrderGT (k + 1) := by
  exact ⟨TreewidthDuality.no_large_bramble, fun h =>
    TreewidthDuality.width_of_decomposable (TreewidthDuality.decomposable_of_bramble_bound h)⟩

end MetaMathlibExt
