/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE GRAPH (clique graph recognition) is NP-complete

Source:
L. Alcón, L. Faria, C. M. H. de Figueiredo and M. Gutierrez, "The complexity of clique graph
recognition", Theoretical Computer Science 410(21-23) (2009), 2072-2083,
doi:10.1016/j.tcs.2009.01.018.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CliqueGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueGraphRecognition

/-!
# CLIQUE GRAPH (clique graph recognition) is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected). QUESTION: is there a graph `H`
such that `G = K(H)`? Here a clique of `H` is a maximal complete set of vertices, and the
clique graph `K(H)` is the intersection graph of the cliques of `H`: one vertex per clique,
two cliques adjacent when they share a vertex. Alcón, Faria, de Figueiredo and Gutierrez
(2009) proved this problem, CLIQUE GRAPH, NP-complete (membership via the Roberts-Spencer
characterization; hardness from a version of 3SAT).

The graph `G` is given by an edge list on `Fin n`. A complete set of `H` is Mathlib's
`SimpleGraph.IsClique` on `Set V`, and a clique in the source's sense (a maximal complete
set) is `Maximal H.IsClique`, Mathlib's formulation of a maximal clique
(`SimpleGraph.isMaximalClique_iff`). `cliqueGraph H` has the maximal cliques of `H` as its
vertices; two distinct maximal cliques are adjacent when their intersection is nonempty
(`SimpleGraph.fromRel` adds distinctness and symmetry). `G = K(H)` is read up to graph
isomorphism (`≃g`), and `H` ranges over all finite simple graphs, each isomorphic to a graph
on some `Fin m`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLIQUE GRAPH (clique graph recognition) is NP-complete.** Source: Alcón, Faria,
de Figueiredo and Gutierrez (2009). -/
public theorem_wanted cliqueGraphRecognition_npComplete :
    cliqueGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.CliqueGraphRecognition
