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

variable {V : Type*}

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

end

end MetaMathlibExt
