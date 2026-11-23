/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT ON PLANAR BIPARTITE GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, the problem
restricted here;
T. Akiyama, T. Nishizeki and N. Saito, "NP-completeness of the Hamiltonian cycle problem for
bipartite graphs", Journal of Information Processing 3 (1980), 73-76;
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM Journal
on Computing 11 (1982), 676-686, doi:10.1137/0211056.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitPlanarBipartiteSubcubic

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT ON PLANAR BIPARTITE GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is bipartite, planar, and has maximum
degree at most 3 (ISGCI class `gc_1055`, bipartite ∩ maximum degree 3 ∩ planar).
QUESTION: does `G` contain a Hamiltonian circuit, i.e. a simple cycle through every vertex?

This is HAMILTONIAN CIRCUIT (Garey and Johnson [GT37]) restricted to planar bipartite graphs of
maximum degree 3. Akiyama, Nishizeki and Saito prove it NP-complete for this class; Itai,
Papadimitriou and Szwarcfiter use it as the source problem of their grid-graph reduction. Membership
in NP is immediate (the circuit is a certificate).

The instance, the graph and the question are those of HAMILTONIAN CIRCUIT
(`HamiltonianCycleUndirectedWanted`), reused unchanged: a vertex count `n` and an edge list on
`Fin n` (`HamiltonianCycleUndirected.HamiltonianCycleUndirectedInstance`,
`HamiltonianCycleUndirected.Graph`), the parent's well-formedness
(`HamiltonianCycleUndirected.WellFormed`: `0 < n` and a simple edge list), and the question
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible` (`3 ≤ n` and Mathlib's
`SimpleGraph.IsHamiltonian`: a cycle through every vertex). The restriction adds that the graph is
bipartite (Mathlib's `SimpleGraph.IsBipartite`, a proper 2-coloring), planar (MathlibExt's
`SimpleGraph.IsPlanar`, a crossing-free straight-line drawing, which by Fáry's theorem is equivalent
to planarity), and has every vertex of degree at most 3.

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
/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (`0 < n`, simple
edge list) whose graph is bipartite, planar, and has every vertex of degree at most 3. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsBipartite ∧ (Graph i).IsPlanar ∧
    ∀ v, (Graph i).degree v ≤ 3

open Classical in
/-- HAMILTONIAN CIRCUIT ON PLANAR BIPARTITE GRAPHS OF MAXIMUM DEGREE 3 as a decision problem over
bitstrings. -/
noncomputable def hamiltonianCircuitPlanarBipartiteSubcubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT ON PLANAR BIPARTITE GRAPHS OF MAXIMUM DEGREE 3 is NP-complete.** Source:
Garey and Johnson (1979), [GT37]; Akiyama, Nishizeki and Saito (1980). -/
public theorem_wanted hamiltonianCircuitPlanarBipartiteSubcubic_npComplete :
    hamiltonianCircuitPlanarBipartiteSubcubicDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitPlanarBipartiteSubcubicDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitPlanarBipartiteSubcubic
