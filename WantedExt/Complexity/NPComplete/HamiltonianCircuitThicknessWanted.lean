/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on graphs of thickness at most k (fixed k ≥ 1) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, comment
("Remains NP-complete (1) if G is planar, cubic, 3-connected, and has no face with fewer than 5
edges [Garey, Johnson, and Tarjan, 1976a]");
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5(4) (1976), 704-714, doi:10.1137/0205049;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1
(thickness-k graphs, HAMILTONIAN CIRCUIT: NP-complete, citing Garey and Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitThickness

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on graphs of thickness at most k is NP-complete

Fix an integer `k ≥ 1`.
INSTANCE: a graph `G = (V, E)` of thickness at most `k`.
QUESTION: does `G` contain a Hamiltonian circuit?

Johnson (1985) defines the thickness-`k` graphs as the "graphs `G = (V, E)` where `E` can be
partitioned into sets `E₁` through `E_k` such that `Gᵢ = (V, Eᵢ)` is planar, `1 ≤ i ≤ k`", for a
fixed `k`, and lists HAMILTONIAN CIRCUIT as NP-complete for them, citing Garey and Johnson, who
record that it remains NP-complete for planar cubic 3-connected graphs (Garey, Johnson and
Tarjan 1976). A planar graph has thickness at most `1 ≤ k` (all edges in `E₁`), so those
instances are instances of this problem for every fixed `k ≥ 1`. Membership in NP: the
certificate is a Hamiltonian circuit together with the partition `E₁, …, E_k`; the circuit is
checked directly and each `Gᵢ` by a polynomial-time planarity test.

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted` ([GT37]: a simple graph on
`Fin n` given by an edge list; a Hamiltonian circuit needs at least three vertices). The
restriction adds that the graph has thickness at most `k`: the question of GRAPH THICKNESS
(`GraphThickness.GraphThicknessFeasible` from
`WantedExt.Complexity.NPComplete.GraphThicknessWanted`) holds for the same vertex count and
edge list with the bound `k` (`withThickness`): the edges are split into `k` classes, each
spanning a planar subgraph on all vertices, with the shared straight-line planarity predicate
`SimpleGraph.IsPlanar` (by Fáry's theorem, planarity for finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The GRAPH THICKNESS instance with the same vertex count and edge list and the bound `k`. -/
def withThickness (k : ℕ) (i : HamiltonianCycleUndirectedInstance) :
    GraphThickness.GraphThicknessInstance :=
  (i.1, i.2, k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: a well-formed HAMILTONIAN
CIRCUIT instance (a simple edge list on `Fin n`, `n > 0`) whose graph has thickness at most
`k`. -/
def WellFormed (k : ℕ) (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧
    GraphThickness.GraphThicknessFeasible (withThickness k i)

open Classical in
/-- HAMILTONIAN CIRCUIT on graphs of thickness at most `k`, for the fixed `k`, as a decision
problem over bitstrings. -/
noncomputable def hamiltonianCircuitThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed k i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on graphs of thickness at most `k` is NP-complete for every fixed
`k ≥ 1`.** Source: Garey and Johnson (1979), [GT37], comment; Garey, Johnson and Tarjan (1976);
Johnson (1985), Table 1. -/
public theorem_wanted hamiltonianCircuitThickness_npComplete (k : ℕ) (_hk : 1 ≤ k) :
    hamiltonianCircuitThicknessDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (hamiltonianCircuitThicknessDec k)

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitThickness
