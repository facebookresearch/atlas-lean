/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Oppositions and opposition matchings

An opposition pairs each vertex with a non-neighbor. These pairs form an opposition matching
in the complement, and swapping the ends of such a matching recovers an opposition.
-/

namespace MetaMathlibExt

@[expose] public section

variable {V W : Type*}

/-- **Oppositions.** An opposition of a graph $G$ is an automorphism $f$ of $G$ such that for
every vertex $v$, $f(f(v)) = v$, $f(v) \neq v$, and $f(v)$ is not adjacent to $v$; that is, an
involutive automorphism moving every vertex outside its closed neighbourhood.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1 (after
Kakihara). -/
def IsOpposition (G : SimpleGraph V) (f : G ≃g G) : Prop :=
  ∀ v, f (f v) = v ∧ f v ≠ v ∧ ¬ G.Adj v (f v)

/-- **Opposable graphs.** A graph $G$ is opposable if it has an opposition: an automorphism $f$
of $G$ such that for every vertex $v$, $f(f(v)) = v$, $f(v) \neq v$, and $f(v)$ is not adjacent
to $v$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def IsOpposable (G : SimpleGraph V) : Prop :=
  ∃ f : G ≃g G, IsOpposition G f

/-- **Opposition matchings.** Let $K$ be a graph. A subgraph $M$ of $K$ is an opposition matching
of $K$ if it is a perfect matching of $K$ and for any two distinct edges $ab$ and $cd$ of $M$,
$ac \in E(K) \iff bd \in E(K)$ and $ad \in E(K) \iff bc \in E(K)$.

Since both matching edges are present, this says that $K$ induces on $\{a, b, c, d\}$ either
$K_4$, a $4$-cycle, or just the two matching edges.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (opposition matchings). -/
def IsOppositionMatching (K : SimpleGraph V) (M : K.Subgraph) : Prop :=
  M.IsPerfectMatching ∧ ∀ a b c d, M.Adj a b → M.Adj c d → s(a, b) ≠ s(c, d) →
    (K.Adj a c ↔ K.Adj b d) ∧ (K.Adj a d ↔ K.Adj b c)

/-- **Oppositions and opposition matchings.** A graph $G$ is opposable if and only if its
complement $\overline{G}$ has an opposition matching.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 1. -/
theorem isOpposable_iff_exists_oppositionMatching (G : SimpleGraph V) :
    IsOpposable G ↔ ∃ M : Gᶜ.Subgraph, IsOppositionMatching Gᶜ M := by
  constructor
  · rintro ⟨f, hf⟩
    let M : Gᶜ.Subgraph :=
      { verts := Set.univ
        Adj := fun v w => w = f v
        adj_sub := fun {v w} h => h ▸ ⟨(hf v).2.1.symm, (hf v).2.2⟩
        edge_vert := fun _ => Set.mem_univ _
        symm := ⟨fun v w h => h ▸ (hf v).1.symm⟩ }
    refine ⟨M, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr (fun v => ?_), ?_⟩
    · exact ⟨f v, rfl, fun _ h => h⟩
    · rintro a b c d (rfl : b = f a) (rfl : d = f c) _
      have hmap (v w : V) : Gᶜ.Adj v w ↔ Gᶜ.Adj (f v) (f w) :=
        (SimpleGraph.Embedding.complEquiv f.toEmbedding).map_adj_iff.symm
      exact ⟨hmap a c, by simpa only [(hf c).1] using hmap a (f c)⟩
  · rintro ⟨M, hperfect, hpairs⟩
    choose mate hmate using fun v =>
      (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hperfect v).exists
    have hinv : Function.Involutive mate := fun v =>
      hperfect.1.eq_of_adj_left (hmate (mate v)) (M.adj_symm (hmate v))
    have hmap (a b : V) : Gᶜ.Adj (mate a) (mate b) ↔ Gᶜ.Adj a b := by
      by_cases h : s(a, mate a) = s(b, mate b)
      · rcases Sym2.eq_iff.mp h with ⟨rfl, _⟩ | ⟨hab, hba⟩
        · simp
        · rw [hba, ← hab]
          exact Gᶜ.adj_comm _ _
      · exact (hpairs _ _ _ _ (hmate a) (hmate b) h).1.symm
    let e : Gᶜ ↪g Gᶜ := ⟨⟨mate, hinv.injective⟩, hmap _ _⟩
    refine ⟨⟨hinv.toPerm mate, (SimpleGraph.Embedding.complEquiv.symm e).map_adj_iff⟩, fun v => ?_⟩
    have hv := (G.compl_adj _ _).mp (M.adj_sub (hmate v))
    exact ⟨hinv v, hv.1.symm, hv.2⟩

/-- **Almost opposable graph.** A graph $G$ is almost opposable if there are a vertex $u$ and a
set $S$ of vertices with $u \in S \subseteq N[u]$, where $N[u]$ is the closed neighbourhood of $u$
($u$ together with its neighbours), such that the subgraph $G - S$ induced on the vertices
outside $S$ is opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 4 (almost opposable graphs). -/
def IsAlmostOpposable (G : SimpleGraph V) : Prop :=
  ∃ u : V, ∃ S : Set V, u ∈ S ∧ S ⊆ insert u (G.neighborSet u) ∧ IsOpposable (G.induce Sᶜ)

/-- **Graph product given by a Boolean formula.** Let $G$ and $H$ be graphs with vertex sets $V$
and $W$, and let $\varphi$ be a Boolean function of four Boolean arguments. The product
$G \varphi H$ is the graph on $V \times W$ in which two distinct vertices $(g_1, h_1)$ and
$(g_2, h_2)$ are adjacent exactly when
$\varphi(g_1 g_2 \in E(G), h_1 h_2 \in E(H), g_1 = g_2, h_1 = h_2)$ is true.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (graph products `GφH`). -/
def formulaProduct [DecidableEq V] [DecidableEq W] (φ : Bool → Bool → Bool → Bool → Bool)
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    SimpleGraph (V × W) :=
  SimpleGraph.fromRel fun x y => φ (G.Adj x.1 y.1) (H.Adj x.2 y.2) (x.1 = y.1) (x.2 = y.2)

/-- **Strong product of graphs.** For simple graphs $G$ on $V$ and $H$ on $W$, the strong
product $G \boxtimes H$ is the simple graph on $V \times W$ in which $(g_1, h_1)$ and
$(g_2, h_2)$ are adjacent if and only if $g_1 = g_2$ and $h_1 h_2$ is an edge of $H$, or
$g_1 g_2$ is an edge of $G$ and $h_1 = h_2$, or $g_1 g_2$ is an edge of $G$ and $h_1 h_2$ is
an edge of $H$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (table of
products). -/
abbrev strongProd [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : SimpleGraph (V × W) :=
  formulaProduct (fun eG eH qG qH => (qG && eH) || (eG && qH) || (eG && eH)) G H

/-- Adjacency in the strong product consists of an edge in one coordinate with equality in
 the other, or edges in both coordinates. -/
theorem strongProd_adj [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (x y : V × W) : (strongProd G H).Adj x y ↔
      x.1 = y.1 ∧ H.Adj x.2 y.2 ∨ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨
        G.Adj x.1 y.1 ∧ H.Adj x.2 y.2 := by
  simp only [strongProd, formulaProduct, SimpleGraph.fromRel_adj, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  rw [eq_comm (a := y.1) (b := x.1), eq_comm (a := y.2) (b := x.2),
    G.adj_comm y.1 x.1, H.adj_comm y.2 x.2, or_self, or_assoc]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact fun e => h.ne (congrArg Prod.snd e)
  · exact fun e => h.ne (congrArg Prod.fst e)
  · exact fun e => h.ne (congrArg Prod.fst e)

/-- **Strong products with a graph that has a universal vertex.** Let $G$ and $H$ be graphs. If
$G$ is almost opposable and $H$ has a universal vertex, that is, a vertex adjacent to every other
vertex of $H$, then the strong product $G \boxtimes H$ is almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 6. -/
theorem isAlmostOpposable_strongProd [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsAlmostOpposable G) (hH : ∃ v, ∀ w, w ≠ v → H.Adj v w) :
    IsAlmostOpposable (strongProd G H) := by
  obtain ⟨u, S, hu, hS, f, hf⟩ := hG
  obtain ⟨v, hv⟩ := hH
  let T := S ×ˢ (Set.univ : Set W)
  refine ⟨(u, v), T, ⟨hu, Set.mem_univ _⟩, ?_, ?_⟩
  · rintro ⟨x, y⟩ hx
    rw [Set.mem_insert_iff, SimpleGraph.mem_neighborSet, strongProd_adj]
    rcases Set.mem_insert_iff.mp (hS hx.1) with heq | hadj
    · by_cases hy : y = v
      · exact Or.inl (Prod.ext heq hy)
      · exact Or.inr (Or.inl ⟨heq.symm, hv y hy⟩)
    · by_cases hy : y = v
      · exact Or.inr (Or.inr (Or.inl ⟨hadj, hy.symm⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hadj, hv y hy⟩))
  -- On the remaining vertices, apply the opposition in the first coordinate only.
  let first (x : ↥Tᶜ) : ↥Sᶜ := ⟨x.1.1, fun hx => x.2 ⟨hx, Set.mem_univ _⟩⟩
  let lift (x : ↥Tᶜ) : ↥Tᶜ := ⟨(f (first x), x.1.2), fun hx => (f (first x)).2 hx.1⟩
  have hinv : Function.Involutive lift := by
    intro x
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (hf (first x)).1) rfl
  have hmap (x y : ↥Tᶜ) :
      ((strongProd G H).induce Tᶜ).Adj (lift x) (lift y) ↔
        ((strongProd G H).induce Tᶜ).Adj x y := by
    have hEq : (f (first x) : V) = (f (first y) : V) ↔ x.1.1 = y.1.1 := by
      change (↑(f (first x)) : V) = ↑(f (first y)) ↔ (first x : V) = (first y : V)
      simp only [Subtype.coe_inj, f.injective.eq_iff]
    have hAdj : G.Adj (f (first x) : V) (f (first y) : V) ↔ G.Adj x.1.1 y.1.1 :=
      f.map_adj_iff
    simp only [SimpleGraph.induce_adj, strongProd_adj]
    dsimp only [lift]
    rw [hEq, hAdj]
  refine ⟨⟨hinv.toPerm lift, hmap _ _⟩, fun x => ⟨hinv x, ?_, ?_⟩⟩
  · intro hx
    exact (hf (first x)).2.1 (congrArg first hx)
  · intro hx
    rcases (strongProd_adj G H _ _).mp (SimpleGraph.induce_adj.mp hx) with
      ⟨heq, _⟩ | ⟨hadj, _⟩ | ⟨hadj, _⟩
    · exact (hf (first x)).2.1 (Subtype.ext heq.symm)
    · exact (hf (first x)).2.2 hadj
    · exact (hf (first x)).2.2 hadj

end

end MetaMathlibExt
