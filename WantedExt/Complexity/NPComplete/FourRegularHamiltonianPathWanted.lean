/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH IN 4-REGULAR GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH;
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical Computer
Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6;
ISGCI (Information System on Graph Classes and their Inclusions), class 4-regular (gc_1101),
problem Hamiltonian path: NP-complete [Picouleau 1994].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FourRegularHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph HamiltonianPathUndirectedFeasible)

/-!
# HAMILTONIAN PATH IN 4-REGULAR GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` in which every vertex has degree 4.
QUESTION: does `G` have a Hamiltonian path, that is, a simple path through every vertex
(endpoints not specified)?

This is HAMILTONIAN PATH (`HamiltonianPathUndirectedWanted`, Garey and Johnson [GT39]) restricted
to 4-regular graphs. Picouleau proves that for every fixed `k ≥ 3` deciding whether a `k`-regular
graph has a Hamiltonian cycle, or a Hamiltonian path, is NP-complete (and, for planar graphs,
NP-complete for `k = 4` and `k = 5`); `k = 4` is this problem. 4-regularity is Mathlib's
`SimpleGraph.IsRegularOfDegree 4` (every vertex has degree 4), as in
`PlanarFourRegularThreeColorabilityWanted`.

The instance, the graph and the question are those of `HamiltonianPathUndirectedWanted`, reused
unchanged: vertex count and edge list on `Fin n`, with `HamiltonianPathUndirected.WellFormed`
(at least one vertex, simple edge list), `HamiltonianPathUndirected.Graph` and
`HamiltonianPathUndirectedFeasible` (a duplicate-free list of all vertices whose consecutive
entries are adjacent). The restriction adds 4-regularity to well-formedness.

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
4-regular. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ (Graph i).IsRegularOfDegree 4

open Classical in
/-- HAMILTONIAN PATH IN 4-REGULAR GRAPHS as a decision problem over bitstrings. -/
noncomputable def fourRegularHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH IN 4-REGULAR GRAPHS is NP-complete.**
Source: Garey and Johnson (1979), [GT39];
Picouleau (1994). -/
public theorem_wanted fourRegularHamiltonianPath_npComplete :
    fourRegularHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fourRegularHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.FourRegularHamiltonianPath
