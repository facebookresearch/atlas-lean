/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for grid graphs is NP-complete

Source:
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics
86(1-3) (1990), 165-177, doi:10.1016/0012-365X(90)90358-O;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetWanted
public import WantedExt.Complexity.NPComplete.GridGraphHamiltonianCircuitWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetGridGraphs

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance gridEdges)

/-!
# DOMINATING SET for grid graphs is NP-complete

INSTANCE: a grid graph `G = (V, E)`, that is, a finite node-induced subgraph of the infinite grid
(the graph on the points of the plane with integer coordinates in which two points are adjacent
when their distance is `1`), and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex not in `V'` is joined to at least one member of `V'`?

This is the restriction of DOMINATING SET ([GT2], `DominatingSetWanted`) to grid graphs. The grid
graph is given by its finite vertex set `V ⊆ ℤ²`, exactly as in
`GridGraphHamiltonianCircuitWanted`, whose definitions are reused: the points are listed without
repetition (`GridGraphHamiltonianCircuit.WellFormed`), an integer coordinate is a pair `(a, b)` of
naturals standing for `a - b`, vertex `u` is the `u`-th point, and the edges are
`GridGraphHamiltonianCircuit.gridEdges`, the pairs `u < v` whose points are adjacent in
MathlibExt's infinite grid `StatMech.Lattice.hypercubicLattice 2`. The question is the parent's
`DominatingSet.DominatingSetFeasible` on the instance with `|V|` vertices, the grid edges and the
bound `K` (`toDominatingSetInstance`), and `WellFormed` adds Garey and Johnson's bounds
`0 < K ≤ |V|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points of `V` (each a pair of integer coordinates, each coordinate an
integer `a - b` given as the pair `(a, b)`) and the bound `K`. -/
abbrev DominatingSetGridGraphsInstance := GridGraphHamiltonianCircuitInstance × ℕ

/-- The grid graph and the bound as a DOMINATING SET instance: `|V|` vertices, the grid edges,
and `K`. -/
def toDominatingSetInstance (i : DominatingSetGridGraphsInstance) :
    DominatingSet.DominatingSetInstance :=
  (i.1.length, gridEdges i.1, i.2)

/-- Well-formedness of an instance: the listed points are pairwise distinct (`V` is a set), and
`0 < K ≤ |V|`. -/
def WellFormed (i : DominatingSetGridGraphsInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i.1 ∧ 0 < i.2 ∧ i.2 ≤ i.1.length

open Classical in
/-- DOMINATING SET for grid graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetGridGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetGridGraphsInstance) x with
  | some i =>
    decide (WellFormed i ∧ DominatingSet.DominatingSetFeasible (toDominatingSetInstance i))
  | none => false

/-- **DOMINATING SET for grid graphs is NP-complete.** Source: Clark, Colbourn and Johnson
(1990); Garey and Johnson (1979), [GT2]. -/
public theorem_wanted dominatingSetGridGraphs_npComplete :
    dominatingSetGridGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetGridGraphsDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetGridGraphs
