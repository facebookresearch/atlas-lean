/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on maximal planar graphs is NP-complete

Source:
A. Wigderson, "The complexity of the Hamiltonian circuit problem for maximal planar graphs",
Technical Report 298, EECS Department, Princeton University (1982) (the report was not
available); the result is recorded by C. Chen, "Any maximal planar graph with only one separating
triangle is Hamiltonian", Journal of Combinatorial Optimization 7(1) (2003), 79-86,
doi:10.1023/A:1021998507140 (abstract: "Chvátal and Wigderson had independently shown that the
problem of determining whether a maximal planar graph is hamiltonian is NP-complete"), and by
F. R. K. Chung, F. T. Leighton and A. L. Rosenberg, "Embedding graphs in books: a layout problem
with applications to VLSI design", SIAM Journal on Algebraic and Discrete Methods 8 (1987),
33-58, doi:10.1137/0608002;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitMaximalPlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT on maximal planar graphs is NP-complete

INSTANCE: a maximal planar graph `G = (V, E)`, that is, a planar graph to which no edge can be
added without destroying planarity (a triangulation).
QUESTION: does `G` contain a Hamiltonian circuit, i.e. a simple cycle through every vertex?

This is HAMILTONIAN CIRCUIT ([GT37], `HamiltonianCycleUndirectedWanted`) restricted to maximal
planar graphs. The instance, the graph and the question are the parent's
(`HamiltonianCycleUndirected.HamiltonianCycleUndirectedInstance`,
`HamiltonianCycleUndirected.Graph`,
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible`: `3 ≤ n` and Mathlib's
`SimpleGraph.IsHamiltonian`), and `WellFormed` is the parent's (`0 < n` and a simple edge list on
`Fin n`) plus the restriction. Planarity is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free
straight-line drawing, which by Fáry's theorem exists exactly for planar graphs). Maximality: for
any two distinct non-adjacent vertices `u` and `v`, the graph with the edge `uv` added
(`G ⊔ SimpleGraph.edge u v`) is not planar.

Membership in NP: the circuit is a certificate, and maximal planarity is decidable in polynomial
time (a planar graph on `n ≥ 3` vertices is maximal planar exactly when it has `3n - 6` edges).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (`0 < n`, simple
edge list on `Fin n`) whose graph is maximal planar: planar, and adding an edge between any two
distinct non-adjacent vertices gives a non-planar graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsPlanar ∧
    ∀ u v : Fin i.1, u ≠ v → ¬ (Graph i).Adj u v → ¬ (Graph i ⊔ SimpleGraph.edge u v).IsPlanar

open Classical in
/-- HAMILTONIAN CIRCUIT on maximal planar graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitMaximalPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on maximal planar graphs is NP-complete.** Source: Wigderson (1982), as
recorded by Chen (2003) and Chung, Leighton and Rosenberg (1987); Garey and Johnson (1979),
[GT37]. -/
public theorem_wanted hamiltonianCircuitMaximalPlanar_npComplete :
    hamiltonianCircuitMaximalPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitMaximalPlanarDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitMaximalPlanar
