/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on cubic planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 199, problem [GT39] HAMILTONIAN PATH,
comment: "Remains NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", where
restriction (1) of [GT37] is "if `G` is planar, cubic, 3-connected, and has no face with fewer
than 5 edges" [Garey, Johnson and Tarjan, 1976a];
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049;
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1102` (cubic ∩
planar), problem Hamiltonian path: NP-complete (Garey, Johnson and Tarjan 1976; Picouleau 1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-!
# HAMILTONIAN PATH on cubic planar graphs is NP-complete

INSTANCE: a planar cubic graph `G = (V, E)` (every vertex has degree exactly `3`).
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (the
endpoints are not specified)?

This is HAMILTONIAN PATH on the ISGCI class `gc_1102` (cubic ∩ planar). The instance, its
well-formedness (a simple graph on `Fin n`, `n ≥ 1`, given by an edge list)
and the question (a list of all vertices, each once, consecutive vertices adjacent) are those of
`WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted` ([GT39]). The
restriction adds Mathlib's `SimpleGraph.IsRegularOfDegree 3` and the repository's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing,
`MathlibExt.Combinatorics.SimpleGraph.Planarity`; by Fáry's theorem these are the planar
graphs).

Garey and Johnson record HAMILTONIAN PATH as NP-complete for planar, cubic, 3-connected graphs
with no face of fewer than `5` edges ([GT39], comment, from [GT37] and Garey, Johnson and
Tarjan); those graphs are planar and cubic, so this restriction is NP-complete as well.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is
cubic (every vertex has degree exactly `3`) and planar. -/
def CubicPlanarWellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  WellFormed i ∧ (Graph i).IsRegularOfDegree 3 ∧ (Graph i).IsPlanar

open Classical in
/-- HAMILTONIAN PATH on cubic planar graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathCubicPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (CubicPlanarWellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH on cubic planar graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT39],
comment; Garey, Johnson and Tarjan (1976); ISGCI (`gc_1102`). -/
public theorem_wanted hamiltonianPathCubicPlanar_npComplete :
    hamiltonianPathCubicPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathCubicPlanarDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicPlanar
