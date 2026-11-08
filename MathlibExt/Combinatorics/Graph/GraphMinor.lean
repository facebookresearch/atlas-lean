/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite graphs and the graph-minor relation
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt

/-- Bundled finite simple graph: a vertex type together with its finiteness
witness and a simple graph on it. The witness is an instance-implicit field,
so it is synthesized by typeclass search at construction; downstream code
still accesses it explicitly as `G.fin`, since instances cannot depend on a
locally bound graph.
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
structure FinGraph where
  V : Type*
  [fin : Finite V]
  G : SimpleGraph V

/-! ## Complete graphs as `FinGraph`s -/

/-- The complete graph on `n` vertices, `Kₙ`, as a bundled finite graph. -/
abbrev cliqueFinGraph (n : ℕ) : FinGraph where
  V := Fin n
  G := SimpleGraph.completeGraph (Fin n)

/-- Adjacency in `Kₙ` is inequality of vertices. -/
theorem cliqueFinGraph_adj {n : ℕ} {x y : Fin n} :
    (cliqueFinGraph n).G.Adj x y ↔ x ≠ y := by
  show (SimpleGraph.completeGraph (Fin n)).Adj x y ↔ x ≠ y
  rw [SimpleGraph.completeGraph_eq_top]
  exact SimpleGraph.top_adj _ _

/-- Single-step minor operation: `iso` is relabelling up to graph isomorphism;
`deleteVertex` is deletion of exactly one vertex (induced subgraph missing the
image of one vertex); `deleteEdge` is deletion of exactly one edge (vertices
identified up to an equivalence, edge sets agree except for one distinguished
edge); `contractEdge` collapses exactly one adjacent pair (a surjective map
identifying a single adjacent pair `a, b` and injective otherwise, with
adjacency in `H` given by images of adjacent pairs in `G` at distinct vertices,
so no loop is forced at the identified vertex).
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
inductive MinorStep : FinGraph → FinGraph → Prop where
  | iso (H G : FinGraph) (e : H.G ≃g G.G) : MinorStep H G
  | deleteVertex (H G : FinGraph) (f : H.V ↪ G.V)
      (h_induced : ∀ u v, H.G.Adj u v ↔ G.G.Adj (f u) (f v))
      (a : G.V) (h_missing : ∀ x, (∃ y, f y = x) ↔ x ≠ a) : MinorStep H G
  | deleteEdge (H G : FinGraph) (e : H.V ≃ G.V)
      (h_sub : ∀ u v, H.G.Adj u v → G.G.Adj (e u) (e v))
      (x y : G.V) (h_edge : G.G.Adj x y)
      (h_miss : ¬H.G.Adj (e.symm x) (e.symm y))
      (h_only : ∀ u v, G.G.Adj (e u) (e v) →
        H.G.Adj u v ∨ (e u = x ∧ e v = y) ∨ (e u = y ∧ e v = x)) :
      MinorStep H G
  | contractEdge (H G : FinGraph) (f : G.V → H.V)
      (hsurj : Function.Surjective f)
      (a b : G.V) (h_adj : G.G.Adj a b) (h_ne : a ≠ b)
      (h_collapse : f a = f b)
      (h_single : ∀ x y, f x = f y →
        x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
      (h_adj_iff : ∀ u v, H.G.Adj u v ↔
        u ≠ v ∧ ∃ u' v', f u' = u ∧ f v' = v ∧ G.G.Adj u' v') :
      MinorStep H G

/-- Graph-minor relation: `H` is a minor of `G` if `H` is obtainable from `G`
by a sequence of isomorphisms, single-vertex deletions, single-edge deletions,
and single-edge contractions.
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
def IsMinor (H G : FinGraph) : Prop :=
  Relation.ReflTransGen MinorStep H G

/-- The minor relation is reflexive. -/
theorem IsMinor.refl (G : FinGraph) : IsMinor G G :=
  Relation.ReflTransGen.refl

/-- The minor relation is transitive. -/
theorem IsMinor.trans {H K G : FinGraph} :
    IsMinor H K → IsMinor K G → IsMinor H G :=
  Relation.ReflTransGen.trans

/-- A single minor step yields a minor. -/
theorem IsMinor.of_step {H G : FinGraph} (h : MinorStep H G) : IsMinor H G :=
  Relation.ReflTransGen.single h

/-- Isomorphic graphs are mutual minors in one step. -/
theorem IsMinor.of_iso {H G : FinGraph} (e : H.G ≃g G.G) : IsMinor H G :=
  IsMinor.of_step (MinorStep.iso H G e)

end MetaMathlibExt
