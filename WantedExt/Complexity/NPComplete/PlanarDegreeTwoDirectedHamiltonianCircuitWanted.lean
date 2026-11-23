/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED HAMILTONIAN CIRCUIT (planar, in- and out-degree at most 2) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT38] DIRECTED HAMILTONIAN CIRCUIT
(comment: NP-complete for planar digraphs, citing Plesník's 1978 manuscript);
J. Plesník, "The NP-completeness of the Hamiltonian cycle problem in planar digraphs with
degree bound two", Information Processing Letters 8(4) (1979), 199-201,
doi:10.1016/0020-0190(79)90023-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleDirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarDegreeTwoDirectedHamiltonianCircuit

/-!
# DIRECTED HAMILTONIAN CIRCUIT (planar, in- and out-degree at most 2) is NP-complete

An instance is a directed graph `G = (V, A)` without loops or multiple arcs that is planar and
in which every vertex has in-degree at most 2 and out-degree at most 2. The question is whether
`G` has a directed Hamiltonian circuit: a directed cycle through every vertex exactly once.
Plesník (1979) proved this NP-complete, improving the bound 3 of Garey, Johnson and Tarjan.

The digraph has vertices `Fin n` and is given by its arc list (`(u, v)` is the arc `u → v`);
opposite arcs `u → v` and `v → u` may both be present. A digraph is planar when its underlying
undirected graph is, so planarity is the shared MathlibExt predicate `SimpleGraph.IsPlanar`
applied to `Cslib.Complexity.Karp.edgeGraph n A`, the simple graph joining `u` and `v` when
either arc is present. The instance type, the base well-formedness (at least one vertex,
distinct loop-free arcs in range) and the directed Hamiltonian circuit are those of
`HamiltonianCycleDirectedWanted`, reused unchanged: a circuit is a list of all vertices in which
consecutive vertices, including the last and the first, are joined by an arc in the forward
direction. This module adds only planarity and the degree bounds.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and arc list, as in
`HamiltonianCycleDirectedWanted`. -/
abbrev PlanarDegreeTwoDirectedHamiltonianCircuitInstance :=
  HamiltonianCycleDirected.HamiltonianCycleDirectedInstance

/-- The underlying undirected simple graph: `u` and `v` are adjacent when `u ≠ v` and `u → v`
or `v → u` is an arc. -/
def UnderlyingGraph (i : PlanarDegreeTwoDirectedHamiltonianCircuitInstance) :
    SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the directed-Hamiltonian-circuit instance is well-formed
(at least one vertex; distinct arcs with endpoints in range, no loops); the underlying graph is
planar; and every vertex has in-degree at most 2 and out-degree at most 2. -/
def WellFormed (i : PlanarDegreeTwoDirectedHamiltonianCircuitInstance) : Prop :=
  HamiltonianCycleDirected.WellFormed i ∧ (UnderlyingGraph i).IsPlanar ∧
    ∀ v < i.1, (i.2.filter fun a => a.2 = v).length ≤ 2 ∧
      (i.2.filter fun a => a.1 = v).length ≤ 2

/-- A directed Hamiltonian circuit, exactly as in `HamiltonianCycleDirectedWanted`. -/
def PlanarDegreeTwoDirectedHamiltonianCircuitFeasible
    (i : PlanarDegreeTwoDirectedHamiltonianCircuitInstance) : Prop :=
  HamiltonianCycleDirected.HamiltonianCycleDirectedFeasible i

open Classical in
/-- DIRECTED HAMILTONIAN CIRCUIT (planar, in- and out-degree at most 2) as a decision problem
over bitstrings. -/
noncomputable def planarDegreeTwoDirectedHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarDegreeTwoDirectedHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ PlanarDegreeTwoDirectedHamiltonianCircuitFeasible i)
  | none => false

/-- **DIRECTED HAMILTONIAN CIRCUIT (planar, in- and out-degree at most 2) is NP-complete.**
Source: Garey and Johnson (1979), [GT38]; Plesník (1979). -/
public theorem_wanted planarDegreeTwoDirectedHamiltonianCircuit_npComplete :
    planarDegreeTwoDirectedHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarDegreeTwoDirectedHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.PlanarDegreeTwoDirectedHamiltonianCircuit
