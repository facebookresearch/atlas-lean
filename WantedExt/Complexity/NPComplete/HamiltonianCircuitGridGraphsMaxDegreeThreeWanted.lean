/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT IN GRID GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

Source:
C. H. Papadimitriou and U. V. Vazirani, "On two geometric problems related to the travelling
salesman problem", Journal of Algorithms 5 (1984), 231-246, doi:10.1016/0196-6774(84)90029-4;
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM Journal
on Computing 11 (1982), 676-686, doi:10.1137/0211056;
E. M. Arkin, S. P. Fekete, K. Islam, H. Meijer, J. S. B. Mitchell, Y. Núñez-Rodríguez,
V. Polishchuk, D. Rappaport and H. Xiao, "Not being (super)thin or solid is hard: A study of grid
Hamiltonicity", Computational Geometry 42 (2009), 582-605, doi:10.1016/j.comgeo.2008.11.004.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GridGraphHamiltonianCircuitWanted
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGridGraphsMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance toHamiltonianInstance)

/-!
# HAMILTONIAN CIRCUIT IN GRID GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

INSTANCE: a grid graph `G` (a finite node-induced subgraph of the infinite grid: a finite set of
points of `ℤ²`, two points adjacent when at distance `1`) in which every vertex has degree at most 3
(ISGCI class `gc_1114`, grid graph ∩ maximum degree 3).
QUESTION: does `G` have a Hamiltonian circuit?

Itai, Papadimitriou and Szwarcfiter prove HAMILTONIAN CIRCUIT NP-complete for grid graphs;
Papadimitriou and Vazirani prove it NP-complete already for grid graphs of maximum degree 3 (Arkin
et al., Section 2: "Papadimitriou and Vazirani proved that the Hamiltonian cycle problem on square
grids is NP-complete, even when restricted to subcubic grids"). Membership in NP is immediate (the
circuit is a certificate).

This restricts HAMILTONIAN CIRCUIT IN GRID GRAPHS (`GridGraphHamiltonianCircuitWanted`), whose
instance, well-formedness and question are reused unchanged: the list of points of `V` (each integer
coordinate `a - b` given as a pair `(a, b)`), pairwise distinct
(`GridGraphHamiltonianCircuit.WellFormed`), and the question
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible` of the grid graph
`GridGraphHamiltonianCircuit.toHamiltonianInstance i` (its `|V|` vertices and grid edges). The
restriction adds that every vertex of that grid graph has degree at most 3.

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
/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT IN GRID GRAPHS instance
(pairwise distinct points) whose grid graph has every vertex of degree at most 3. -/
def WellFormed (i : GridGraphHamiltonianCircuitInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i ∧
    ∀ v, (HamiltonianCycleUndirected.Graph (toHamiltonianInstance i)).degree v ≤ 3

open Classical in
/-- HAMILTONIAN CIRCUIT IN GRID GRAPHS OF MAXIMUM DEGREE 3 as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitGridGraphsMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GridGraphHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible
      (toHamiltonianInstance i))
  | none => false

/-- **HAMILTONIAN CIRCUIT IN GRID GRAPHS OF MAXIMUM DEGREE 3 is NP-complete.** Source: Papadimitriou
and Vazirani (1984); Itai, Papadimitriou and Szwarcfiter (1982). -/
public theorem_wanted hamiltonianCircuitGridGraphsMaxDegreeThree_npComplete :
    hamiltonianCircuitGridGraphsMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitGridGraphsMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGridGraphsMaxDegreeThree
