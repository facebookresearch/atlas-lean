/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH for bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH, p. 199
(comment: "Remains NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", where
restriction (2) of [GT37] is "if G is bipartite [Krishnamoorthy, 1975]");
M. S. Krishnamoorthy, "An NP-hard problem in bipartite graphs", SIGACT News 7 (1975), 26,
doi:10.1145/990518.990521;
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM
Journal on Computing 11 (1982), 676-686, doi:10.1137/0211056.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBipartite

open HamiltonianPathUndirected (HamiltonianPathUndirectedInstance Graph
  HamiltonianPathUndirectedFeasible)

/-!
# HAMILTONIAN PATH for bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)`.
QUESTION: does `G` contain a Hamiltonian path?

Garey and Johnson record that HAMILTONIAN PATH remains NP-complete for bipartite graphs, the
restriction under which Krishnamoorthy proved HAMILTONIAN CIRCUIT NP-complete. Itai,
Papadimitriou and Szwarcfiter prove HAMILTONIAN PATH NP-complete for grid graphs (stated on
`main` as `WantedExt.Complexity.NPComplete.GridGraphHamiltonianPathWanted`), which are
bipartite, so the bipartite problem is NP-hard; a Hamiltonian path is a polynomial
certificate.

The instance, the graph and the question are those of HAMILTONIAN PATH
(`HamiltonianPathUndirectedWanted`), reused unchanged: a vertex count `n` and an edge list on
`Fin n`, the parent's well-formedness (`0 < n` and a simple edge list), and the parent's
question (an ordering of all vertices in which consecutive vertices are adjacent). The
restriction adds that the graph is bipartite: Mathlib's `SimpleGraph.IsBipartite`
(`Colorable 2`), as in `FeedbackVertexSetBipartiteWanted` and
`HamiltonianPathChordalBipartiteWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN PATH for bipartite graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT39], comment; Krishnamoorthy (1975); Itai, Papadimitriou and Szwarcfiter (1982). -/
public theorem_wanted hamiltonianPathBipartite_npComplete :
    hamiltonianPathBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBipartite
