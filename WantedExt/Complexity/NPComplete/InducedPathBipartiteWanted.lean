/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED PATH for bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT23] INDUCED PATH, comment ("Remains
NP-complete if G is bipartite"), attributed to M. Yannakakis, "Node- and edge-deletion
NP-complete problems", Proceedings of the 10th Annual ACM Symposium on Theory of Computing
(STOC 1978), 253-264, doi:10.1145/800133.804355.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import WantedExt.Complexity.NPComplete.InducedPathWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedPathBipartite

open MetaMathlibExt.Complexity.NPComplete.InducedPath (InducedPathInstance InducedPathFeasible)

/-!
# INDUCED PATH for bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≥ K` such that the subgraph induced by `V'` is a
simple path on `|V'|` vertices?

This is INDUCED PATH (Garey and Johnson [GT23], `InducedPathWanted`) restricted to bipartite
graphs; the comment to [GT23] reads "Remains NP-complete if G is bipartite", with the reference
[Yannakakis, 1978c]. The instance type, the graph, the parent's well-formedness (a simple edge
list and `0 < K ≤ |V|`) and the question are those of `InducedPathWanted`; the restriction adds
that the graph is bipartite (Mathlib's `SimpleGraph.IsBipartite`, that is, `Colorable 2`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed INDUCED PATH instance whose graph is
bipartite. -/
def WellFormed (i : InducedPathInstance) : Prop :=
  InducedPath.WellFormed i ∧ (InducedPath.Graph i).IsBipartite

open Classical in
/-- INDUCED PATH for bipartite graphs as a decision problem over bitstrings. -/
noncomputable def inducedPathBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedPathInstance) x with
  | some i => decide (WellFormed i ∧ InducedPathFeasible i)
  | none => false

/-- **INDUCED PATH for bipartite graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT23]; Yannakakis (1978). -/
public theorem_wanted inducedPathBipartite_npComplete :
    inducedPathBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedPathBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.InducedPathBipartite
