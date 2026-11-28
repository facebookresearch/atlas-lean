/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOPOLARITY OF TRIANGLE-FREE GRAPHS is NP-complete

Source:
R. Churchley and J. Huang, "On the polarity and monopolarity of graphs", Journal of Graph Theory
76 (2014), 138-148, doi:10.1002/jgt.21755;
ISGCI (Information System on Graph Classes and their Inclusions), class triangle-free (gc_371),
problem Monopolarity: NP-complete [Churchley and Huang 2014].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MonopolarityTriangleFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFree

/-!
# MONOPOLARITY OF TRIANGLE-FREE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with no triangle.
QUESTION: is `G` monopolar, that is, can `V` be partitioned into a stable set and a set inducing a
disjoint union of cliques?

Churchley and Huang (abstract): "we prove that recognizing polarity or monopolarity remains
NP-complete for triangle-free graphs". Monopolarity is the repository's existing definition
`ThreeColorabilityMonopolar.IsMonopolar` (from the merged `ThreeColorabilityMonopolarWanted`):
some vertex set `A` is independent (Mathlib's `SimpleGraph.IsIndepSet`) and its complement
induces a cluster graph (`ClusterDeletion.IsClusterGraph`: any two distinct vertices joined by a
walk are adjacent, so every component is a clique). Triangle-freeness is Mathlib's
`SimpleGraph.CliqueFree 3`.

The instance is a vertex count and an edge list on `Fin n`, with the usual simple-edge-list
well-formedness, and the graph is `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MONOPOLARITY OF TRIANGLE-FREE GRAPHS is NP-complete.**
Source: Churchley and Huang (2014). -/
public theorem_wanted monopolarityTriangleFree_npComplete :
    monopolarityTriangleFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monopolarityTriangleFreeDec

end MetaMathlibExt.Complexity.NPComplete.MonopolarityTriangleFree
