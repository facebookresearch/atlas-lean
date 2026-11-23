/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH for undirected path graphs is NP-complete

Source:
A. A. Bertossi and M. A. Bonuccelli, "Hamiltonian circuits in interval graph generalizations",
Information Processing Letters 23(4) (1986), 195-200, doi:10.1016/0020-0190(86)90135-3;
ISGCI, Information System on Graph Classes and their Inclusions, class undirected path (gc_129,
https://www.graphclasses.org/classes/gc_129.html), problem Hamiltonian path;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsWanted
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirectedPathGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance HamiltonianPathUndirectedFeasible)

/-!
# HAMILTONIAN PATH for undirected path graphs is NP-complete

INSTANCE: an undirected path graph `G = (V, E)`, that is, the vertex intersection graph of a
family of paths in an undirected tree.
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path that goes through every vertex
(endpoints not specified)?

This is the restriction of HAMILTONIAN PATH (`HamiltonianPathUndirectedWanted`) to undirected
path graphs. The instance type and the question are the parent's
(`HamiltonianPathUndirected.HamiltonianPathUndirectedInstance`: vertex count and edge list;
`HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible`: a list of all vertices without
repetition whose consecutive entries are adjacent), and `WellFormed` is the parent's (a simple
edge list on `Fin n`, `0 < n`) plus the restriction. Undirected path graphs are the
repository's `DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph`: for some tree `T`
(Mathlib's `SimpleGraph.IsTree`), each vertex `v` has the vertex set of a path in `T` (a
`SimpleGraph.Walk` with `IsPath`), and distinct vertices are adjacent exactly when their paths
share a vertex of `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`, `0 < n`), and
the graph is an undirected path graph. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧
    DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph (HamiltonianPathUndirected.Graph i)

open Classical in
/-- HAMILTONIAN PATH for undirected path graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathUndirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH for undirected path graphs is NP-complete.** Source: Bertossi and
Bonuccelli (1986); ISGCI (gc_129); Garey and Johnson (1979), [GT39]. -/
public theorem_wanted hamiltonianPathUndirectedPathGraphs_npComplete :
    hamiltonianPathUndirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathUndirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirectedPathGraphs
