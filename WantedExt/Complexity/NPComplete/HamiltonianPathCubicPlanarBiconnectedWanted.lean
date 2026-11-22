/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on 2-connected cubic planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 199, problem [GT39] HAMILTONIAN PATH,
comment: "Remains NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", where
restriction (1) of [GT37] is "if `G` is planar, cubic, 3-connected, and has no face with fewer
than 5 edges" [Garey, Johnson and Tarjan, 1976a];
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049;
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"2-connected ∩ cubic ∩ planar" (gc_1183), problem Hamiltonian path: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianPathCubicPlanarWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanarBiconnected

open HamiltonianPathUndirected (HamiltonianPathUndirectedInstance Graph
  HamiltonianPathUndirectedFeasible)

/-!
# HAMILTONIAN PATH on 2-connected cubic planar graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is 2-connected, cubic (every vertex
has degree exactly `3`) and planar.
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (the
endpoints are not specified)?

This is HAMILTONIAN PATH ([GT39], `HamiltonianPathUndirectedWanted`) on the ISGCI class
"2-connected ∩ cubic ∩ planar" (`gc_1183`). The instance type, the graph and the question (a list
of all vertices, each once, consecutive vertices adjacent) are HAMILTONIAN PATH's;
well-formedness is that of HAMILTONIAN PATH on cubic planar graphs
(`HamiltonianPathCubicPlanarWanted`: a simple graph on `Fin n`, `n ≥ 1`, given by an edge list,
Mathlib's `SimpleGraph.IsRegularOfDegree 3` and the repository's `SimpleGraph.IsPlanar`), plus
2-connectivity, the shared MathlibExt predicate `SimpleGraph.IsVertexConnected 2` (more than two
vertices, and connected after deleting any single vertex), as in
`HamiltonianCircuitCubicPlanarBiconnectedWanted`.

Garey and Johnson record HAMILTONIAN PATH as NP-complete for planar, cubic, 3-connected graphs
with no face of fewer than `5` edges ([GT39], comment, from restriction (1) of [GT37] and Garey,
Johnson and Tarjan). Those graphs are 2-connected, cubic and planar, so HAMILTONIAN PATH on this
larger class is NP-hard as well; membership in NP holds for all graphs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed instance of HAMILTONIAN PATH on cubic planar
graphs whose graph is also 2-connected. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathCubicPlanar.CubicPlanarWellFormed i ∧ (Graph i).IsVertexConnected 2

open Classical in
/-- HAMILTONIAN PATH on 2-connected cubic planar graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathCubicPlanarBiconnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH on 2-connected cubic planar graphs is NP-complete.** Source: Garey and
Johnson (1979), [GT39], comment; Garey, Johnson and Tarjan (1976); ISGCI (`gc_1183`). -/
public theorem_wanted hamiltonianPathCubicPlanarBiconnected_npComplete :
    hamiltonianPathCubicPlanarBiconnectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathCubicPlanarBiconnectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanarBiconnected
