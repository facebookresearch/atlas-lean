/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# TOPOLOGICAL MINOR TESTING: definitions

INSTANCE: graphs `G = (V, E)` and `H = (V_H, E_H)`.
QUESTION: does `G` contain a subdivision of `H` as a subgraph, i.e., does `G` contain a subgraph
homeomorphic to `H`?

Garey and Johnson ([OPEN2]) define the question for a fixed `H` as: does `G` contain a subgraph
`G' = (V', E')` that can be converted to a graph isomorphic to `H` by repeatedly removing any
vertex of degree 2 and adding the edge joining its two neighbors? For fixed `H` its complexity
is listed as open; their comment records that the problem is NP-complete when `H` is part of the
instance, the version stated here. For a graph `G` with `n ≥ 3` vertices and `H` the cycle on
`n` vertices, a subdivision of `H` inside `G` has at least `n` vertices, hence no subdivision
vertices, so it is a Hamiltonian circuit of `G`, and conversely a Hamiltonian circuit is such a
subgraph; this is the special case HAMILTONIAN CIRCUIT ([GT37], Karp 1972).

A subdivision of `H` in `G` is stated directly: a one-to-one map `φ : V_H → V` (the branch
vertices) and, for each edge `{a, b}` of `H`, a path in `G` from `φ a` to `φ b`, such that no
path passes through a branch vertex other than its two ends, and paths of different edges share
no vertex other than branch vertices (they are internally vertex-disjoint). This is equivalent
to Garey and Johnson's formulation. Suppressing the inner vertices of the paths turns such a
subgraph into `H`. Conversely, a step "remove a vertex of degree 2 and add the edge joining its
two neighbors" undoes the subdivision of an edge when the two neighbors are not adjacent; when
they are adjacent, it deletes a vertex if graphs stay simple, and creates a parallel edge that
no later step removes if they are read as multigraphs (so it never occurs on the way to the
simple graph `H`). Undoing a subdivision and deleting a vertex both preserve containing a
subdivision of the result.

The vertices of `G` are `0, …, n - 1` and those of `H` are `0, …, m - 1`; both graphs are given
by simple edge lists (no loops, no repeated edge in either orientation, endpoints in range), so
the entries of `H`'s list are its edges, one each. Paths are Mathlib walks `p : G.Walk u v` with
`p.IsPath`, as in `DisjointConnectingPathsWanted`; path `j` realizes the `j`-th edge of `H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN2] SUBGRAPH HOMEOMORPHISM
(FOR A FIXED GRAPH H), p. 285, comment: "If H is allowed to vary as part of the instance, the
problem is NP-complete, since it contains HAMILTONIAN CIRCUIT as a special case";
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9
(HAMILTONIAN CIRCUIT, Garey and Johnson's [GT37]).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting

/-- An instance: the vertex count `n` and edge list of `G`, and the vertex count `m` and edge
list of `H`. -/
abbrev TopologicalMinorTestingInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The host graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TopologicalMinorTestingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: both edge lists are simple (endpoints in range, no
self-loops, no repeated or reversed edges). -/
def WellFormed (i : TopologicalMinorTestingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.Nodup ∧
      ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2)

/-- `G` contains a subdivision of `H`: a one-to-one map `φ` from the vertices of `H` to those of
`G`, and for each edge `(a, b)` of `H` (the `j`-th list entry) a path in `G` from `φ a` to
`φ b`, such that every branch vertex `φ c` on path `j` is one of its two ends, and every vertex
common to two different paths is a branch vertex. -/
def TopologicalMinorTestingFeasible (i : TopologicalMinorTestingInstance) : Prop :=
  ∃ (φ : Fin i.2.2.1 → Fin i.1)
    (paths : Fin i.2.2.2.length → (u : Fin i.1) × (v : Fin i.1) × (Graph i).Walk u v),
    Function.Injective φ ∧
    (∀ j, ∃ a b : Fin i.2.2.1, (a : ℕ) = (i.2.2.2.get j).1 ∧ (b : ℕ) = (i.2.2.2.get j).2 ∧
      (paths j).1 = φ a ∧ (paths j).2.1 = φ b ∧ (paths j).2.2.IsPath) ∧
    (∀ j, ∀ w ∈ (paths j).2.2.support, ∀ c, φ c = w → w = (paths j).1 ∨ w = (paths j).2.1) ∧
    ∀ j l, j ≠ l → ∀ w ∈ (paths j).2.2.support, w ∈ (paths l).2.2.support → ∃ c, φ c = w

open Classical in
/-- TOPOLOGICAL MINOR TESTING as a decision problem over bitstrings. -/
noncomputable def topologicalMinorTestingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TopologicalMinorTestingInstance) x with
  | some i => decide (WellFormed i ∧ TopologicalMinorTestingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting
