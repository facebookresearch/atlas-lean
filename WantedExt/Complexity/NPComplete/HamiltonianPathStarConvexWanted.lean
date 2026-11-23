/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on star convex bipartite graphs is NP-complete

Source:
H. Chen, Z. Lei, T. Liu, Z. Tang, C. Wang and K. Xu, "Complexity of domination, Hamiltonicity
and treewidth for tree convex bipartite graphs", Journal of Combinatorial Optimization 32 (2016),
95-110, doi:10.1007/s10878-015-9917-3;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the unrestricted
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class star convex (gc_1151),
problem Hamiltonian path: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetStarConvexWanted
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathStarConvex

open HamiltonianPathUndirected (HamiltonianPathUndirectedInstance Graph
  HamiltonianPathUndirectedFeasible)

/-!
# HAMILTONIAN PATH on star convex bipartite graphs is NP-complete

INSTANCE: a star convex bipartite graph `G = (V, E)`.
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (the
endpoints are not specified)?

A bipartite graph `B = (X, Y, E)` is star convex (ISGCI class `gc_1151`) if there is a tree `T`
on `X` that is a star such that, for every `y ∈ Y`, the neighbourhood of `y` induces a subtree of
`T`. The class predicate is `FeedbackVertexSetStarConvex.IsStarConvex`
(`FeedbackVertexSetStarConvexWanted`, which explains its reading of the definition). The instance
type, the graph, the well-formedness (a simple graph on `Fin n`, `n ≥ 1`, given by an edge list)
and the question (a list of all vertices, each once, consecutive vertices adjacent) are those of
HAMILTONIAN PATH ([GT39], `HamiltonianPathUndirectedWanted`); this module adds the class
restriction to well-formedness.

Chen, Lei, Liu, Tang, Wang and Xu prove seven problems, Hamiltonian cycle and Hamiltonian path
among them, NP-complete for tree convex bipartite graphs even when the associated trees are
stars. Membership in NP holds for all graphs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is star
convex bipartite. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ FeedbackVertexSetStarConvex.IsStarConvex (Graph i)

open Classical in
/-- HAMILTONIAN PATH on star convex bipartite graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathStarConvexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH on star convex bipartite graphs is NP-complete.** Source: Chen, Lei, Liu,
Tang, Wang and Xu (2016); Garey and Johnson (1979), [GT39]; ISGCI (`gc_1151`). -/
public theorem_wanted hamiltonianPathStarConvex_npComplete :
    hamiltonianPathStarConvexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathStarConvexDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathStarConvex
