/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH IN GRID GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

Source:
C. H. Papadimitriou and U. V. Vazirani, "On two geometric problems related to the travelling
salesman problem", Journal of Algorithms 5 (1984), 231-246, doi:10.1016/0196-6774(84)90029-4;
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM
Journal on Computing 11 (1982), 676-686, doi:10.1137/0211056;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1114` (grid graph ∩
maximum degree 3), problem Hamiltonian path: NP-complete (Papadimitriou and Vazirani 1984).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GridGraphMaxDegreeThreeHamiltonianPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GridGraphMaxDegreeThreeHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance toHamiltonianInstance)
open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedFeasible)

/-!
# HAMILTONIAN PATH IN GRID GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

INSTANCE: a finite nonempty set `V` of points of `ℤ²` whose grid graph `G` (an edge between two
points exactly when they are at Euclidean distance `1`) has maximum degree at most `3`.
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (the
endpoints are not specified)?

This is HAMILTONIAN PATH on the ISGCI class `gc_1114` (grid graph ∩ maximum degree 3). A grid graph
is a finite node-induced subgraph of the infinite grid (Itai, Papadimitriou and
Szwarcfiter). The instance, its well-formedness and the grid graph are those of
`WantedExt.Complexity.NPComplete.GridGraphHamiltonianCircuitWanted`: the listed points of `ℤ²`,
pairwise distinct, and `GridGraphHamiltonianCircuit.toHamiltonianInstance`, the graph on the
points whose edges join points at distance `1` (adjacency in MathlibExt's
`StatMech.Lattice.hypercubicLattice 2`). The question is HAMILTONIAN PATH
(`HamiltonianPathUndirectedWanted`, [GT39]) on that graph: its `WellFormed` (at least one
vertex; the grid edge list is always simple) and `HamiltonianPathUndirectedFeasible` are reused
unchanged.
The degree bound is added to well-formedness with Mathlib's `SimpleGraph.degree`.

Papadimitriou and Vazirani prove HAMILTONIAN PATH NP-complete on grid graphs of maximum degree
`3` (strengthening Itai, Papadimitriou and Szwarcfiter), and use it to show the Euclidean
degree-3 minimum spanning tree problem NP-hard.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN PATH IN GRID GRAPHS OF MAXIMUM DEGREE 3 is NP-complete.** Source: Papadimitriou
and Vazirani (1984); Itai,
Papadimitriou and Szwarcfiter (1982); ISGCI (`gc_1114`); Garey and Johnson (1979), [GT39]. -/
public theorem_wanted gridGraphMaxDegreeThreeHamiltonianPath_npComplete :
    gridGraphMaxDegreeThreeHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L gridGraphMaxDegreeThreeHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.GridGraphMaxDegreeThreeHamiltonianPath
