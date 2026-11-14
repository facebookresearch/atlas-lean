/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT IN GRID GRAPHS is NP-complete

Source:
A. Itai, C. H. Papadimitriou and J. L. Szwarcfiter, "Hamilton paths in grid graphs", SIAM
Journal on Computing 11 (1982), 676-686, doi:10.1137/0211056.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.VecNotation
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT IN GRID GRAPHS is NP-complete

INSTANCE: a finite set `V` of points of `ℤ²`; the grid graph `G` on `V` has an edge between two
points exactly when they are at Euclidean distance `1`.
QUESTION: does `G` have a Hamiltonian circuit?

A grid graph is a finite node-induced subgraph of the infinite grid, the graph on the points of
the plane with integer coordinates in which two points are adjacent when their distance is `1`
(Itai, Papadimitriou and Szwarcfiter 1982). The infinite grid is MathlibExt's
`StatMech.Lattice.hypercubicLattice 2` on `StatMech.Lattice.Site 2 = (Fin 2 → ℤ)`, whose
adjacency is `ℓ¹`-distance one; for integer points this is Euclidean distance one. The question
is HAMILTONIAN CIRCUIT (`HamiltonianCycleUndirectedWanted`) restricted to grid graphs, given by
their points.

The instance lists the points of `V`, without repetition; an integer coordinate is a pair
`(a, b)` of naturals standing for `a - b`. Vertex `u` is the `u`-th point, and the grid graph is
passed to `HamiltonianCycleUndirected` as the instance with `|V|` vertices and the edge list
`gridEdges`: the pairs `u < v` whose sites are adjacent in `hypercubicLattice 2`. That edge list
has no repeated edge, no loop and no reversed copy, so it is a well-formed
`HamiltonianCycleUndirected` edge list, and the question is that module's
`HamiltonianCycleUndirectedFeasible`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points of `V`, each a pair of integer coordinates, each coordinate an
integer `a - b` given as the pair `(a, b)`. -/
abbrev GridGraphHamiltonianCircuitInstance := List ((ℕ × ℕ) × (ℕ × ℕ))

/-- The site of `ℤ²` encoded by a pair of coordinate pairs. -/
def site (p : (ℕ × ℕ) × (ℕ × ℕ)) : StatMech.Lattice.Site 2 :=
  ![(p.1.1 : ℤ) - p.1.2, (p.2.1 : ℤ) - p.2.2]

/-- Adjacency in `hypercubicLattice 2` is decidable: it is an equation between naturals. -/
instance (x y : StatMech.Lattice.Site 2) :
    Decidable ((StatMech.Lattice.hypercubicLattice 2).Adj x y) :=
  inferInstanceAs (Decidable ((∑ j, (x j - y j).natAbs) = 1))

/-- Well-formedness of an instance: the listed points are pairwise distinct (`V` is a set). -/
def WellFormed (i : GridGraphHamiltonianCircuitInstance) : Prop :=
  (i.map site).Nodup

/-- The edges of the grid graph: the pairs `(u, v)` with `u < v < |V|` whose sites are adjacent
in the infinite grid `hypercubicLattice 2`. -/
def gridEdges (i : GridGraphHamiltonianCircuitInstance) : List (ℕ × ℕ) :=
  (List.range i.length).flatMap fun u =>
    ((List.range i.length).filter fun v =>
      decide (u < v ∧ (StatMech.Lattice.hypercubicLattice 2).Adj (site (i.getD u ((0, 0), (0, 0))))
        (site (i.getD v ((0, 0), (0, 0)))))).map fun v => (u, v)

/-- The grid graph as a HAMILTONIAN CIRCUIT instance: `|V|` vertices and the grid edges. -/
def toHamiltonianInstance (i : GridGraphHamiltonianCircuitInstance) :
    HamiltonianCycleUndirectedInstance :=
  (i.length, gridEdges i)

open Classical in
/-- HAMILTONIAN CIRCUIT IN GRID GRAPHS as a decision problem over bitstrings. -/
noncomputable def gridGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GridGraphHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible (toHamiltonianInstance i))
  | none => false

/-- **HAMILTONIAN CIRCUIT IN GRID GRAPHS is NP-complete.** Source: Itai, Papadimitriou and
Szwarcfiter (1982). -/
public theorem_wanted gridGraphHamiltonianCircuit_npComplete :
    gridGraphHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L gridGraphHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
