/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT23] INDUCED PATH;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 4, the connected node-deletion problem, for
the property "is a path").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedPath

/-!
# INDUCED PATH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a subset
`V' ⊆ V` with `|V'| ≥ K` such that the subgraph induced by `V'` is a simple path on `|V'|`
vertices?

"The subgraph induced by `V'` is a simple path on `|V'|` vertices" is Mathlib's induced
containment `(SimpleGraph.pathGraph m).IsIndContained G` with `m = |V'|`: an embedding
`pathGraph m ↪g G` is injective and both preserves and reflects adjacency, so its range `V'` has
`m` vertices and induces a copy of the path graph on `m` vertices
(`SimpleGraph.isIndContained_iff_exists_iso_induce`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev InducedPathInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : InducedPathInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K ≤ |V|`. -/
def WellFormed (i : InducedPathInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of `m ≥ K` vertices induces a simple path on `m` vertices: the path graph on `m`
vertices is an induced subgraph of the instance graph. -/
def InducedPathFeasible (i : InducedPathInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ (SimpleGraph.pathGraph m).IsIndContained (Graph i)

open Classical in
/-- INDUCED PATH as a decision problem over bitstrings. -/
noncomputable def inducedPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedPathInstance) x with
  | some i => decide (WellFormed i ∧ InducedPathFeasible i)
  | none => false

/-- **INDUCED PATH is NP-complete.** Source: Garey and Johnson (1979), [GT23];
Yannakakis (1978), Theorem 4. -/
public theorem_wanted inducedPath_npComplete :
    inducedPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedPathDec

end MetaMathlibExt.Complexity.NPComplete.InducedPath
