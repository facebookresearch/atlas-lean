/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SnortOppositions

/-!
# Gluing oppositions of blocks

Compatible oppositions on the induced subgraphs of a vertex partition glue to an
opposition of the whole graph.
-/

namespace MetaMathlibExt

-- Match the section context that determines the wanted theorem's universe names.
variable {V W : Type*}

/-- **Gluing oppositions of blocks.** Let $G$ be a graph, let $p$ be a map from its vertices to
an index set, with blocks $B_i = \{v : p(v) = i\}$, and let $f$ be a map from the vertices of $G$
to themselves. Suppose that for every index $i$ there is an opposition of the subgraph of $G$
induced on $B_i$ that agrees with $f$ on $B_i$, and that for all vertices $u, w$ with
$p(u) \neq p(w)$ we have $uw \in E(G) \iff f(u)f(w) \in E(G)$ and
$uf(w) \in E(G) \iff f(u)w \in E(G)$. Then $G$ is opposable.

Since $uf(u)$ and $wf(w)$ are non-edges, the second condition says that the four vertices
$u, f(u), w, f(w)$ induce $C_4$, $2K_2$ or $4K_1$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 2. -/
public theorem isOpposable_of_blocks {ι : Type*} (G : SimpleGraph V) (p : V → ι)
    (f : V → V)
    (hf : ∀ i, ∃ φ : G.induce {v | p v = i} ≃g G.induce {v | p v = i},
      IsOpposition _ φ ∧ ∀ x, (φ x : V) = f x)
    (hpair : ∀ u w, p u ≠ p w →
      (G.Adj u w ↔ G.Adj (f u) (f w)) ∧ (G.Adj u (f w) ↔ G.Adj (f u) w)) :
    IsOpposable G := by
  have hlocal (v : V) : f (f v) = v ∧ f v ≠ v ∧ ¬ G.Adj v (f v) := by
    obtain ⟨φ, hφ, hagree⟩ := hf (p v)
    let x : {w // p w = p v} := ⟨v, rfl⟩
    have hfx : (φ x : V) = f v := hagree x
    obtain ⟨hinv, hne, hnonadj⟩ := hφ x
    refine ⟨?_, ?_, ?_⟩
    · rw [← hfx, ← hagree (φ x), hinv]
    · intro heq
      exact hne (Subtype.ext (hfx.trans heq))
    · simpa only [SimpleGraph.induce_adj, hfx] using hnonadj
  have hmap (u w : V) : G.Adj (f u) (f w) ↔ G.Adj u w := by
    by_cases h : p u = p w
    · obtain ⟨φ, _, hagree⟩ := hf (p w)
      let x : {v // p v = p w} := ⟨u, h⟩
      let y : {v // p v = p w} := ⟨w, rfl⟩
      simpa only [SimpleGraph.induce_adj, hagree] using φ.map_adj_iff (v := x) (w := y)
    · exact (hpair u w h).1.symm
  have hinv : Function.Involutive f := fun v => (hlocal v).1
  exact ⟨⟨hinv.toPerm f, hmap _ _⟩, hlocal⟩

end MetaMathlibExt
