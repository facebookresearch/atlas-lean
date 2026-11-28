/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED HAMILTONIAN CIRCUIT (planar, in- and out-degree at most 2): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT38] DIRECTED HAMILTONIAN CIRCUIT
(comment: NP-complete for planar digraphs, citing Plesník's 1978 manuscript);
J. Plesník, "The NP-completeness of the Hamiltonian cycle problem in planar digraphs with
degree bound two", Information Processing Letters 8(4) (1979), 199-201,
doi:10.1016/0020-0190(79)90023-1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleDirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarDegreeTwoDirectedHamiltonianCircuit

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

end MetaMathlibExt.Complexity.NPComplete.PlanarDegreeTwoDirectedHamiltonianCircuit
