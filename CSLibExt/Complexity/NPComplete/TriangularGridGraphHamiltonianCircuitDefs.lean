/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT IN TRIANGULAR GRID GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
E. M. Arkin, S. P. Fekete, K. Islam, H. Meijer, J. S. B. Mitchell, Y. Núñez-Rodríguez,
V. Polishchuk, D. Rappaport and H. Xiao, "Not being (super)thin or solid is hard: A study of grid
Hamiltonicity", Computational Geometry: Theory and Applications 42 (2009), 582-605,
doi:10.1016/j.comgeo.2008.11.004, Definition 2.2 and Theorem 3.1;
ISGCI (Information System on Graph Classes and their Inclusions), class triangular grid graph
(gc_1118), problem Hamiltonian cycle: NP-complete [Arkin et al. 2009].
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GridGraphHamiltonianCircuitDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangularGridGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance HamiltonianCycleUndirectedFeasible)
open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance site)

/-- Adjacency in the triangular lattice in the coordinates `(a, b)` of the point
`a • (1, 0) + b • (1/2, √3/2)`: the squared distance `Δa² + Δa Δb + Δb²` is `1`. -/
def TriAdj (x y : StatMech.Lattice.Site 2) : Prop :=
  (x 0 - y 0) * (x 0 - y 0) + (x 0 - y 0) * (x 1 - y 1) + (x 1 - y 1) * (x 1 - y 1) = 1

instance (x y : StatMech.Lattice.Site 2) : Decidable (TriAdj x y) :=
  inferInstanceAs (Decidable (_ = _))

/-- The edges of the triangular grid graph: the pairs `(u, v)` with `u < v < |V|` whose sites
are adjacent in the triangular lattice. -/
def triangularEdges (i : GridGraphHamiltonianCircuitInstance) : List (ℕ × ℕ) :=
  (List.range i.length).flatMap fun u =>
    ((List.range i.length).filter fun v =>
      decide (u < v ∧ TriAdj (site (i.getD u ((0, 0), (0, 0))))
        (site (i.getD v ((0, 0), (0, 0)))))).map fun v => (u, v)

/-- The triangular grid graph as a HAMILTONIAN CIRCUIT instance: `|V|` vertices and the edges
`triangularEdges`. -/
def toHamiltonianInstance (i : GridGraphHamiltonianCircuitInstance) :
    HamiltonianCycleUndirectedInstance :=
  (i.length, triangularEdges i)

open Classical in
/-- HAMILTONIAN CIRCUIT IN TRIANGULAR GRID GRAPHS as a decision problem over bitstrings. -/
noncomputable def triangularGridGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GridGraphHamiltonianCircuitInstance) x with
  | some i =>
    decide (GridGraphHamiltonianCircuit.WellFormed i ∧
      HamiltonianCycleUndirectedFeasible (toHamiltonianInstance i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TriangularGridGraphHamiltonianCircuit
