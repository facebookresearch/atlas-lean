/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT IN TRIANGULAR GRID GRAPHS is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GridGraphHamiltonianCircuitWanted
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangularGridGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance HamiltonianCycleUndirectedFeasible)
open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance site)

/-!
# HAMILTONIAN CIRCUIT IN TRIANGULAR GRID GRAPHS is NP-complete

INSTANCE: a finite set `V` of vertices of the tiling of the plane with unit-side equilateral
triangles; the triangular grid graph `G` on `V` is the subgraph of the tiling induced by `V`.
QUESTION: does `G` have a Hamiltonian circuit?

Arkin et al., Definition 2.2: a triangular grid graph is a plane graph induced by a subset of the
vertices of the tiling of the plane with unit-side equilateral triangles; their Theorem 3.1: "The
HCP for triangular grid graphs is NP-complete". The question is HAMILTONIAN CIRCUIT
(`HamiltonianCycleUndirectedDefs`, Garey and Johnson [GT37]) restricted to these graphs, given
by their vertices.

Coordinates: the vertices of the tiling are the points `a • (1, 0) + b • (1/2, √3/2)` with
integers `a, b`, each with exactly one such pair `(a, b)`. The squared Euclidean distance between
the points of `(a, b)` and `(a', b')` is `Δa² + Δa Δb + Δb²` with `Δa = a - a'`, `Δb = b - b'`,
and two vertices of the tiling are joined by a side of a triangle exactly when their distance is
`1`; so two vertices are adjacent exactly when `Δa² + Δa Δb + Δb² = 1` (`TriAdj`), that is, when
`(Δa, Δb)` is one of `(±1, 0)`, `(0, ±1)`, `±(1, -1)`.

The instance lists the vertices of `V`, without repetition, in the encoding of the merged
`GridGraphHamiltonianCircuitWanted`, whose instance type, `site` and well-formedness
`GridGraphHamiltonianCircuit.WellFormed` (pairwise distinct sites) are reused:
an integer coordinate is a pair `(a, b)` of naturals standing for `a - b`, and `site` gives the
point of `ℤ²`, here read as the pair `(a, b)` above. Vertex `u` is the `u`-th listed vertex, and
the graph is passed to `HamiltonianCycleUndirected` as the instance with `|V|` vertices and the
edge list `triangularEdges`: the pairs `u < v` whose sites satisfy `TriAdj`. That edge list has
no repeated edge, no loop and no reversed copy, and the question is
`HamiltonianCycleUndirectedFeasible` (at least three vertices and a Hamiltonian cycle).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **HAMILTONIAN CIRCUIT IN TRIANGULAR GRID GRAPHS is NP-complete.**
Source: Garey and Johnson (1979), [GT37];
Arkin et al. (2009), Theorem 3.1. -/
public theorem_wanted triangularGridGraphHamiltonianCircuit_npComplete :
    triangularGridGraphHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L triangularGridGraphHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.TriangularGridGraphHamiltonianCircuit
