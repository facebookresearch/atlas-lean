/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Card
public import Mathlib.Order.WellFounded

/-!
# Tree-decompositions and tree-width

A tree-decomposition of a graph `G` is a tree `T` together with a bag `V_t ⊆ V(G)` for every node
`t`, such that the bags cover the vertices (T1) and the edges (T2) of `G`, and every bag on the
path between two nodes contains the intersection of their bags (T3). Its width is the largest
bag size minus one, and the tree-width of `G` is the least width of a tree-decomposition
(Diestel, *Graph Theory*, Sections 12.3–12.4).

Tree-width is recorded as the predicate `SimpleGraph.HasTreewidthAtMost G k`, "`G` has a
tree-decomposition all of whose bags have at most `k + 1` vertices", for `k : ℕ`. This avoids the
numerical convention for the graph with no vertices (whose tree-width is `-1` under the usual
definition, as the empty bag has width `-1`): that graph satisfies `HasTreewidthAtMost G k` for
every `k`.

## Main results

* `SimpleGraph.TreeDecomposition.exists_bag_superset`: every finite clique lies in one bag
  (Diestel, Corollary 12.3.5).
* `SimpleGraph.hasTreewidthAtMost_top_iff`: the complete graph on `n` vertices has tree-width at
  most `k` exactly when `n ≤ k + 1`; that is, `tw(Kₙ) = n - 1` for `n ≥ 1`.
* `SimpleGraph.not_hasTreewidthAtMost_zero_of_adj`: a graph with an edge has tree-width at least
  one.
* `SimpleGraph.IsTree.hasTreewidthAtMost_one`: finite trees have tree-width at most one.

## References

* R. Diestel, *Graph Theory*, 6th edition, Chapter 12 (author's online preview of Chapter 12,
  PDF dated 28 June 2024, https://diestel-graph-theory.com/), Sections 12.3 and 12.4.
-/

@[expose] public section

namespace SimpleGraph

universe u

variable {V : Type u}

/-- **Tree-decomposition.** A tree-decomposition of a graph `G` consists of a finite tree `T` on a
node type `ι` and a bag `bag t ⊆ V` for every node `t`, such that (T1) every vertex lies in some
bag, (T2) both ends of every edge lie in a common bag, and (T3) `bag t₁ ∩ bag t₃ ⊆ bag t₂`
whenever `t₂` lies on the path from `t₁` to `t₃` in `T` (Diestel, *Graph Theory*, 6th ed.,
Section 12.3, conditions (T1)–(T3)). -/
structure TreeDecomposition (G : SimpleGraph V) where
  /-- The nodes of the decomposition tree. -/
  ι : Type u
  /-- The decomposition tree is finite. -/
  [finite : Finite ι]
  /-- The decomposition tree. -/
  T : SimpleGraph ι
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- The bag of each node. -/
  bag : ι → Set V
  /-- (T1): the bags cover the vertices. -/
  cover : ∀ v, ∃ t, v ∈ bag t
  /-- (T2): every edge lies in a bag. -/
  edge_mem : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t
  /-- (T3): bags on the path between two nodes contain the intersection of their bags. -/
  coherent : ∀ (t₁ t₃ t₂ : ι) (p : T.Walk t₁ t₃), p.IsPath → t₂ ∈ p.support →
    bag t₁ ∩ bag t₃ ⊆ bag t₂

namespace TreeDecomposition

variable {G : SimpleGraph V} (D : G.TreeDecomposition)

/-- **Width at most `k`.** A tree-decomposition has width at most `k` if every bag has at most
`k + 1` vertices (Diestel, *Graph Theory*, 6th ed., Section 12.4: the width is
`max {|V_t| - 1 : t ∈ T}`). -/
def HasWidthAtMost (k : ℕ) : Prop :=
  ∀ t, (D.bag t).encard ≤ k + 1

/-- A node `t₀` of the subtree of bags containing `a` that is nearest to `i` lies on a path from
`i` to every other node of that subtree. -/
private theorem exists_isPath_mem_support (a : V) {i t t₀ : D.ι} (ha : a ∈ D.bag t)
    (ha₀ : a ∈ D.bag t₀) (hmin : ∀ s, a ∈ D.bag s → D.T.dist i t₀ ≤ D.T.dist i s) :
    ∃ W : D.T.Walk i t, W.IsPath ∧ t₀ ∈ W.support := by
  classical
  obtain ⟨p₀, hp₀len⟩ := D.isTree.connected.exists_walk_length_eq_dist i t₀
  have hp₀ : p₀.IsPath := p₀.isPath_of_length_eq_dist hp₀len
  obtain ⟨R, hR⟩ := (D.isTree.existsUnique_path t₀ t).exists
  refine ⟨p₀.append R, ?_, by simp⟩
  rw [Walk.isPath_append]
  refine ⟨hp₀, hR.tail, ?_⟩
  intro x hx₁ hx₂
  have hxR : x ∈ R.support := List.mem_of_mem_tail hx₂
  have hxne : x ≠ t₀ := by
    rintro rfl
    have hnd := hR.support_nodup
    cases R with
    | nil => simp at hx₂
    | cons h q =>
      simp only [Walk.support_cons, List.tail_cons] at hx₂ hnd
      exact (List.nodup_cons.mp hnd).1 hx₂
  have hax : a ∈ D.bag x := D.coherent t₀ t x R hR hxR ⟨ha₀, ha⟩
  have hsplit := congrArg Walk.length (p₀.take_spec hx₁)
  rw [Walk.length_append] at hsplit
  have hpos : 0 < (p₀.dropUntil x hx₁).length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hxne)
  have hle : D.T.dist i x ≤ (p₀.takeUntil x hx₁).length := SimpleGraph.dist_le _
  have := hmin x hax
  omega

/-- **Every clique lies in a bag.** For every tree-decomposition of a graph `G` and every finite
set `K` of pairwise adjacent vertices, some bag contains `K` (Diestel, *Graph Theory*, 6th ed.,
Corollary 12.3.5, "every complete subgraph of `G` is contained in some part"). The proof is a
Helly-type argument: for each new vertex `a`, take the node of the subtree of bags containing
`a` nearest to a bag containing the rest; by (T3) it contains the rest. -/
theorem exists_bag_superset (K : Finset V) (hK : ∀ u ∈ K, ∀ w ∈ K, u ≠ w → G.Adj u w) :
    ∃ t, (K : Set V) ⊆ D.bag t := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    obtain ⟨t⟩ := D.isTree.connected.nonempty
    exact ⟨t, by simp⟩
  | insert a K haK ih =>
    obtain ⟨i, hi⟩ := ih fun u hu w hw huw =>
      hK u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw) huw
    have hS : {s | a ∈ D.bag s}.Nonempty := D.cover a
    set t₀ := Function.argminOn (D.T.dist i) {s | a ∈ D.bag s} hS
    have ha₀ : a ∈ D.bag t₀ := Function.argminOn_mem (f := D.T.dist i) _ hS
    have hmin : ∀ s, a ∈ D.bag s → D.T.dist i t₀ ≤ D.T.dist i s :=
      fun s hs => Function.argminOn_le (f := D.T.dist i) {s | a ∈ D.bag s} hs
    refine ⟨t₀, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbK
    · exact ha₀
    · have hab : a ≠ b := fun h => haK (h ▸ hbK)
      obtain ⟨t, hat, hbt⟩ :=
        D.edge_mem a b (hK a (Finset.mem_insert_self a K) b hb hab)
      obtain ⟨W, hW, ht₀W⟩ := D.exists_isPath_mem_support a hat ha₀ hmin
      exact D.coherent i t t₀ W hW ht₀W ⟨hi hbK, hbt⟩

end TreeDecomposition

/-- **Tree-width at most `k`.** A graph `G` has tree-width at most `k` if it has a
tree-decomposition of width at most `k`, that is, one whose bags all have at most `k + 1`
vertices (Diestel, *Graph Theory*, 6th ed., Section 12.4). For a finite vertex type `V` and
`k : ℕ` this is `tw(G) ≤ k`; the graph with no vertices satisfies it for every `k`, matching its
tree-width `-1`. For an infinite vertex type the predicate is always false, since the
decomposition tree is finite and the bags are finite. -/
def HasTreewidthAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : G.TreeDecomposition, D.HasWidthAtMost k

/-- **Tree-width bounds are monotone.** -/
theorem HasTreewidthAtMost.mono {G : SimpleGraph V} {k l : ℕ} (h : G.HasTreewidthAtMost k)
    (hkl : k ≤ l) : G.HasTreewidthAtMost l := by
  obtain ⟨D, hD⟩ := h
  refine ⟨D, fun t => (hD t).trans ?_⟩
  exact_mod_cast Nat.succ_le_succ hkl

/-- **The one-bag decomposition.** A graph on at most `k + 1` vertices has tree-width at most `k`:
put all vertices in the bag of a single-node tree. -/
theorem hasTreewidthAtMost_of_encard_le (G : SimpleGraph V) {k : ℕ}
    (hV : (Set.univ : Set V).encard ≤ k + 1) : G.HasTreewidthAtMost k :=
  ⟨{ ι := PUnit
     T := ⊥
     isTree := IsTree.of_subsingleton
     bag := fun _ => Set.univ
     cover := fun v => ⟨PUnit.unit, Set.mem_univ v⟩
     edge_mem := fun u v _ => ⟨PUnit.unit, Set.mem_univ u, Set.mem_univ v⟩
     coherent := fun _ _ _ _ _ _ => Set.subset_univ _ }, fun _ => hV⟩

/-- **A graph with an edge has tree-width at least one.** Both ends of an edge lie in a common
bag (T2), which therefore has at least two vertices. -/
theorem not_hasTreewidthAtMost_zero_of_adj {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    ¬G.HasTreewidthAtMost 0 := by
  rintro ⟨D, hD⟩
  obtain ⟨t, hu, hv⟩ := D.edge_mem u v huv
  have h2 : ({u, v} : Set V).encard ≤ (D.bag t).encard :=
    Set.encard_le_encard (Set.insert_subset hu (Set.singleton_subset_iff.mpr hv))
  rw [Set.encard_pair (G.ne_of_adj huv)] at h2
  have := (hD t)
  have : (2 : ℕ∞) ≤ 1 := h2.trans (by simpa using this)
  exact absurd this (by decide)

/-- **Tree-width of complete graphs.** For a finite vertex type `V` with `n` elements, the
complete graph on `V` has tree-width at most `k` if and only if `n ≤ k + 1`; that is,
`tw(Kₙ) = n - 1` for `n ≥ 1` (and the graph with no vertices has tree-width at most every `k`).
The lower bound is Diestel, *Graph Theory*, 6th ed., Corollary 12.3.5 applied to the whole
vertex set; the upper bound is the one-bag decomposition. -/
theorem hasTreewidthAtMost_top_iff [Fintype V] {k : ℕ} :
    (⊤ : SimpleGraph V).HasTreewidthAtMost k ↔ Fintype.card V ≤ k + 1 := by
  classical
  constructor
  · rintro ⟨D, hD⟩
    obtain ⟨t, ht⟩ := D.exists_bag_superset Finset.univ fun u _ w _ huw => by simpa using huw
    have h1 : (Set.univ : Set V).encard ≤ (D.bag t).encard :=
      Set.encard_le_encard (by simpa using ht)
    have h2 := h1.trans (hD t)
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card] at h2
    exact_mod_cast h2
  · intro h
    apply hasTreewidthAtMost_of_encard_le
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    exact_mod_cast h

/-- In a tree, a vertex has at most one neighbour that is closer to a fixed root. -/
private theorem IsTree.eq_of_dist_add_one {G : SimpleGraph V} (hG : G.IsTree) (r : V) {v w w' : V}
    (hw : G.Adj w v) (hw' : G.Adj w' v) (hd : G.dist r v = G.dist r w + 1)
    (hd' : G.dist r v = G.dist r w' + 1) : w = w' := by
  obtain ⟨p, hp⟩ := hG.connected.exists_walk_length_eq_dist r w
  obtain ⟨p', hp'⟩ := hG.connected.exists_walk_length_eq_dist r w'
  have hP : (p.concat hw).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [Walk.length_concat, hp, hd])
  have hP' : (p'.concat hw').IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [Walk.length_concat, hp', hd'])
  have heq := congrArg Subtype.val ((hG.isAcyclic.subsingleton_path _ _).elim ⟨_, hP⟩ ⟨_, hP'⟩)
  exact (Walk.concat_inj heq).1

/-- In a tree, the unique path between two vertices is any given path. -/
private theorem IsTree.mem_support_of_isPath {G : SimpleGraph V} (hG : G.IsTree) {a b c : V}
    (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath) (hc : c ∈ p.support) : c ∈ q.support := by
  have := congrArg Subtype.val ((hG.isAcyclic.subsingleton_path _ _).elim ⟨p, hp⟩ ⟨q, hq⟩)
  simp only at this
  exact this ▸ hc

/-- **Trees have tree-width at most one.** Root a finite tree `G` at a vertex `r` and give every
vertex `v` the bag consisting of `v` and its parent (its unique neighbour closer to `r`); with
the tree `G` itself as decomposition tree this is a tree-decomposition with bags of size at most
two (Diestel, *Graph Theory*, 6th ed., Section 12.4: "trees themselves have tree-width 1"; trees
with an edge have tree-width exactly one by `not_hasTreewidthAtMost_zero_of_adj`). -/
theorem IsTree.hasTreewidthAtMost_one [Finite V] {G : SimpleGraph V} (hG : G.IsTree) :
    G.HasTreewidthAtMost 1 := by
  classical
  obtain ⟨r⟩ := hG.connected.nonempty
  let par : V → Set V := fun v => {w | G.Adj w v ∧ G.dist r v = G.dist r w + 1}
  have hpar : ∀ v, (par v).Subsingleton := fun v w hw w' hw' =>
    hG.eq_of_dist_add_one r hw.1 hw'.1 hw.2 hw'.2
  let bag : V → Set V := fun v => insert v (par v)
  have hbag : ∀ x t, x ∈ bag t ↔ t = x ∨ (G.Adj x t ∧ G.dist r t = G.dist r x + 1) := by
    intro x t
    simp only [bag, par, Set.mem_insert_iff, Set.mem_ofPred_eq, eq_comm]
  refine ⟨{ ι := V, T := G, isTree := hG, bag := bag,
            cover := fun v => ⟨v, Set.mem_insert v _⟩,
            edge_mem := ?_, coherent := ?_ }, ?_⟩
  · intro u v huv
    rcases hG.dist_eq_dist_add_one_of_adj r huv with h | h
    · exact ⟨u, Set.mem_insert u _, Or.inr ⟨huv.symm, h⟩⟩
    · exact ⟨v, Or.inr ⟨huv, h⟩, Set.mem_insert v _⟩
  · intro t₁ t₃ t₂ p hp ht₂ x ⟨hx₁, hx₃⟩
    rw [hbag] at hx₁ hx₃ ⊢
    rcases hx₁ with rfl | ⟨h₁, hd₁⟩ <;> rcases hx₃ with h₃ | ⟨h₃, hd₃⟩
    · subst h₃
      cases p with
      | nil => left; simpa using ht₂
      | cons h q => exact absurd hp (by simp)
    · have hq : (Walk.cons h₃ Walk.nil : G.Walk t₁ t₃).IsPath := by
        simp [Walk.isPath_def, G.ne_of_adj h₃]
      have := hG.mem_support_of_isPath p _ hp hq ht₂
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at this
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨h₃, hd₃⟩
    · subst h₃
      have hq : (Walk.cons h₁.symm Walk.nil : G.Walk _ _).IsPath := by
        simp [Walk.isPath_def, G.ne_of_adj h₁.symm]
      have := hG.mem_support_of_isPath p _ hp hq ht₂
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at this
      rcases this with rfl | rfl
      · exact Or.inr ⟨h₁, hd₁⟩
      · exact Or.inl rfl
    · by_cases h13 : t₁ = t₃
      · subst h13
        cases p with
        | nil =>
          simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at ht₂
          subst ht₂
          exact Or.inr ⟨h₁, hd₁⟩
        | cons h q => exact absurd hp (by simp)
      · have hq : (Walk.cons h₁.symm (Walk.cons h₃ Walk.nil) : G.Walk t₁ t₃).IsPath := by
          simp [Walk.isPath_def, G.ne_of_adj h₁.symm, G.ne_of_adj h₃, h13]
        have := hG.mem_support_of_isPath p _ hp hq ht₂
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at this
        rcases this with rfl | rfl | rfl
        · exact Or.inr ⟨h₁, hd₁⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h₃, hd₃⟩
  · intro t
    change (insert t (par t)).encard ≤ ((1 : ℕ) : ℕ∞) + 1
    refine (Set.encard_insert_le _ _).trans ?_
    have : (par t).encard ≤ 1 := Set.encard_le_one_iff.mpr fun a b ha hb => hpar t ha hb
    simpa using add_le_add_right this 1

end SimpleGraph
