/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Grünbaum's conjecture on duals of triangulations (Open Problem Garden 177)

Open Problem Garden, Grunbaum's Conjecture (B. Grünbaum): if `G` is a simple loopless triangulation
of an orientable surface, then the dual of `G` is `3`-edge-colorable.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.GrunbaumTriangulationDualColoringOpenGardenProblem177Wanted

/-!
Source: Open Problem Garden, Grunbaum's Conjecture (node 177; B. Grünbaum),
http://www.openproblemgarden.org/op/grunbaums_conjecture. UnsolvedMath record UM-00003314
(`OPG-177`), dataset ulamai/UnsolvedMath v1.8.0.

A triangulation of a closed orientable surface is an oriented combinatorial map `(D, α, σ)`: a
finite dart set `D`, a fixed-point-free involution `α` (the two darts of an edge) and a permutation
`σ` (rotation of the darts around a vertex), with `⟨α, σ⟩` transitive (connected surface) and every
cycle of the face permutation `φ = σ ∘ α` of length `3`; vertices are the cycles of `σ`. Oriented
maps are the cellular embeddings in orientable surfaces. Simple and loopless: no dart has both ends
at one vertex, and two darts with the same tail and the same head are equal. The dual graph has the
faces as vertices and the edges `{d, α d}` as edges, so a proper `3`-edge-colouring of the dual is a
colouring of the edges with three colours that are distinct around every face; a dual loop (a face
containing both darts of an edge) makes such a colouring impossible, as it should.
-/

variable {D : Type}

/-- A simple loopless triangulation of a closed orientable surface, as an oriented combinatorial map
on the finite dart set `D`: `α` reverses each edge (a fixed-point-free involution), `σ` rotates the
darts around their common vertex, the surface is connected, every face (cycle of `φ = σ ∘ α`) is a
triangle, and the graph of vertices (cycles of `σ`) and edges (pairs `{d, α d}`) has no loops and no
multiple edges. -/
def IsSimpleTriangulation (α σ : Equiv.Perm D) : Prop :=
  (∀ d, α (α d) = d) ∧ (∀ d, α d ≠ d) ∧
    (∀ d d' : D, ∃ τ ∈ Subgroup.closure ({α, σ} : Set (Equiv.Perm D)), τ d = d') ∧
    (∀ d, σ (α (σ (α (σ (α d))))) = d ∧ σ (α d) ≠ d) ∧
    (∀ (d : D) (k : ℕ), (σ ^ k) d ≠ α d) ∧
    ∀ d d' : D, (∃ k : ℕ, (σ ^ k) d = d') → (∃ k : ℕ, (σ ^ k) (α d) = α d') → d = d'

/-- The dual (cubic) graph, whose vertices are the faces and whose edges are the edges `{d, α d}`
(joining the faces on their two sides), is `3`-edge-colorable: there is a colouring of the edges by
`Fin 3` such that the three edges around every face have distinct colours (a dual loop admits no
such colouring). -/
def DualThreeEdgeColorable (α σ : Equiv.Perm D) : Prop :=
  ∃ c : D → Fin 3, (∀ d, c (α d) = c d) ∧ ∀ d, c (σ (α d)) ≠ c d

/-- Grünbaum's conjecture: the dual of every simple loopless triangulation of a closed orientable
surface is `3`-edge-colorable. -/
def grunbaumConjecture : Prop :=
  ∀ (D : Type) [Fintype D] (α σ : Equiv.Perm D), IsSimpleTriangulation α σ →
    DualThreeEdgeColorable α σ

/--
Resolved false: Kochol constructs, on every orientable surface of genus at least `5`, infinitely
many `3`-regular graphs that are not `3`-edge-colorable and have a polyhedral embedding (its dual is
a simple graph). The dual of such an embedding is a simple loopless triangulation whose dual is the
snark itself, so it is a counterexample. Source: Open Problem Garden, Grunbaum's Conjecture (node
177; B. Grünbaum), http://www.openproblemgarden.org/op/grunbaums_conjecture; resolution: M. Kochol,
Polyhedral embeddings of snarks in orientable surfaces, Proc. Amer. Math. Soc. 137 (2009),
1613-1619, abstract: an embedding of a 3-regular graph is polyhedral if its dual is a simple graph;
negative solution to the conjecture that every 3-regular graph with a polyhedral embedding in an
orientable surface is 3-edge-colorable: for each orientable surface of genus at least 5 there are
infinitely many 3-regular non-3-edge-colorable graphs with a polyhedral embedding in the surface,
https://doi.org/10.1090/S0002-9939-08-09698-6.
-/
public theorem_wanted grunbaumConjecture_refuted : ¬ grunbaumConjecture

end MathlibExt.GraphTheory.GrunbaumTriangulationDualColoringOpenGardenProblem177Wanted
