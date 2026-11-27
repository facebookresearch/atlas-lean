/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIPARTITE CONTRACTION is NP-complete

Source:
P. Heggernes, P. van 't Hof, D. Lokshtanov and C. Paul, "Obtaining a bipartite graph by
contracting few edges", SIAM Journal on Discrete Mathematics 27(4) (2013), 2143-2156,
doi:10.1137/130907392 (arXiv:1102.5441), Sections 1, 2 and 5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteContraction

/-!
# BIPARTITE CONTRACTION is NP-complete

INSTANCE: a graph `G = (V, E)` and a nonnegative integer `K`.
QUESTION: can a bipartite graph be obtained from `G` by a sequence of at most `K` edge
contractions, where contracting the edge `xy` replaces `x` and `y` by a new vertex adjacent to
exactly those vertices that were adjacent to at least one of `x` and `y`?

Heggernes, van 't Hof, Lokshtanov and Paul (Section 1) define the problem: "Given a graph `G`
and an integer `k`, can we obtain a bipartite graph from `G` by a sequence of at most `k` edge
contractions in `G`?", with the contraction of Section 2 quoted above ("Every edge contraction
reduces the number of vertices in the graph by exactly one"). Section 5 states that BIPARTITE
CONTRACTION is NP-complete, by a polynomial-time reduction from EDGE BIPARTIZATION that
replaces every edge by a path of sufficiently large odd length.

As in `GraphContractabilityWanted`, a sequence of contractions merges the vertices of `G` into
classes, each inducing a connected subgraph of `G`, and its result is the quotient graph `G.map
f` of the class map `f` (two classes are adjacent exactly when some edge of `G` joins them);
conversely every partition into classes inducing connected subgraphs is reached by contracting
the edges of a spanning tree of each class. Each contraction removes one vertex, so a result
with `m` vertices takes exactly `|V| - m` contractions. Hence the answer is yes exactly when
some `f : V → Fin m` has fibers inducing connected (in particular nonempty) subgraphs, `|V| ≤ m
+ K`, and `G.map f` is bipartite (Mathlib's `SimpleGraph.IsBipartite`, `2`-colorable).

The graph is simple and given by an edge list on `Fin n`. Isolated vertices have no edge to
contract and stay isolated vertices of the result, so they do not change the answer and the
binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K` on the number of
contractions. -/
abbrev BipartiteContractionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BipartiteContractionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BipartiteContractionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- At most `K` edge contractions turn the graph into a bipartite graph: some map
`f : Fin n → Fin m` has fibers inducing connected subgraphs, `n ≤ m + K` (the contractions
number `n - m`), and the quotient graph is bipartite. -/
def BipartiteContractionFeasible (i : BipartiteContractionInstance) : Prop :=
  ∃ (m : ℕ) (f : Fin i.1 → Fin m), (∀ x, ((Graph i).induce {v | f v = x}).Connected) ∧
    i.1 ≤ m + i.2.2 ∧ ((Graph i).map f).IsBipartite

open Classical in
/-- BIPARTITE CONTRACTION as a decision problem over bitstrings. -/
noncomputable def bipartiteContractionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BipartiteContractionInstance) x with
  | some i => decide (WellFormed i ∧ BipartiteContractionFeasible i)
  | none => false

/-- **BIPARTITE CONTRACTION is NP-complete.** Source: Heggernes, van 't Hof, Lokshtanov and
Paul (2013), Section 5. -/
public theorem_wanted bipartiteContraction_npComplete :
    bipartiteContractionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bipartiteContractionDec

end MetaMathlibExt.Complexity.NPComplete.BipartiteContraction
