/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for rooted directed path graphs is NP-complete

Source:
B. S. Panda and D. Pradhan, "NP-completeness of Hamiltonian cycle problem on rooted directed
path graphs", arXiv:0809.2443 (2008), problem Π₁ and Theorem 3.5;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (HAMILTONIAN CIRCUIT for directed path
graphs, open there);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for
the 21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (entry N [98]);
F. Gavril, "A recognition algorithm for the intersection graphs of directed paths in directed
trees", Discrete Mathematics 13 (1975), 237-249, doi:10.1016/0012-365X(75)90021-7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitRootedDirectedPathGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRootedDirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)
open MetaMathlibExt.Complexity.NPComplete.RootedDirectedPathGraphCompletion
  (IsRootedDirectedPathGraph)

/-!
# HAMILTONIAN CIRCUIT for rooted directed path graphs is NP-complete

INSTANCE: a rooted directed path graph `G = (V, E)`: the vertex intersection graph of a family
of directed paths in a rooted directed tree (a tree whose edges are oriented away from a
single root). These are the "directed path graphs" of Johnson's column ("for some root vertex
in the tree, all paths are subpaths of paths from the root to a leaf").
QUESTION: does `G` contain a Hamiltonian circuit?

Panda and Pradhan prove this NP-complete (their problem Π₁, Theorem 3.5), resolving the entry
of Johnson's Table 1 recorded by de Figueiredo, de Melo, Sasaki and Silva. The class is a
proper subclass of the directed path graphs of `HamiltonianCircuitDirectedPathGraphsWanted`,
whose tree orientation is arbitrary, so this is a different problem. Membership in NP: a
Hamiltonian circuit is a polynomial certificate (a yes-instance has `n ≤ |E|`), and rooted
directed path graphs are recognized in polynomial time (Gavril).

The instance, the graph and the question are those of HAMILTONIAN CIRCUIT
(`HamiltonianCycleUndirectedDefs`), reused unchanged as in
`HamiltonianCircuitDirectedPathGraphsWanted`: a vertex count `n` and an edge list on `Fin n`,
the parent's well-formedness (`0 < n` and a simple edge list), and the question
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible` (`3 ≤ n` and Mathlib's
`SimpleGraph.IsHamiltonian`). The restriction adds that the graph is a rooted directed path
graph, the repository's predicate `RootedDirectedPathGraphCompletion.IsRootedDirectedPathGraph`:
for some finite tree `T` with root `r`, each vertex `v` has the vertex set `P v` of a path of
`T` whose every step moves away from `r`, and distinct vertices are adjacent exactly when their
paths share a vertex of `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT for rooted directed path graphs is NP-complete.** Source: Panda and
Pradhan (2008); Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva (2022). -/
public theorem_wanted hamiltonianCircuitRootedDirectedPathGraphs_npComplete :
    hamiltonianCircuitRootedDirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitRootedDirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRootedDirectedPathGraphs
