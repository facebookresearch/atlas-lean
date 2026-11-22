/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX COVER on planar graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT1] VERTEX COVER, p. 190, comment
("Equivalent complexity to INDEPENDENT SET with respect to restrictions on G"), and problem
[GT20] INDEPENDENT SET, p. 195, comment ("Remains NP-complete for cubic planar graphs [Garey,
Johnson, and Stockmeyer, 1976], [Garey and Johnson, 1977a], [Maier and Storer, 1977]");
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32(4) (1977), 826-834, doi:10.1137/0132071;
B. Mohar, "Face covers and the genus problem for apex graphs", Journal of Combinatorial Theory,
Series B 82(1) (2001), 102-117, doi:10.1006/jctb.2000.2026, Theorem 4.1(a).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexCoverPlanarMaxDegreeThree

/-!
# VERTEX COVER on planar graphs of maximum degree 3 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with no vertex degree exceeding `3`, and a positive integer
`K ≤ |V|`.
QUESTION: is there a vertex cover of size `K` or less for `G`, i.e., a subset `V' ⊆ V` with
`|V'| ≤ K` such that for each edge `{u, v} ∈ E` at least one of `u` and `v` belongs to `V'`?

The vertex cover is Mathlib's `SimpleGraph.IsVertexCover` of a `Finset` coerced to a set;
planarity is the repository's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing,
which by Fáry's theorem exists exactly for planar graphs) and the degree bound uses Mathlib's
`SimpleGraph.degree`. The graph is given, as in the sibling modules, by a vertex count `n`
(vertices `Fin n`) and a simple edge list.

Membership in NP: the certificate is `V'`; degrees are checked directly and planarity in linear
time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568). Hardness: `V'` is a vertex cover exactly
when `V - V'` is an independent set, so `(G, K) ↦ (G, |V| - K)` exchanges the two problems on
the same graph ([GT1], comment), and INDEPENDENT SET is NP-complete on cubic planar graphs
([GT20], comment; Mohar, Theorem 4.1(a): "The minimum vertex cover and the maximum independent
set problem are NP-hard also when restricted to 2-connected cubic planar graphs"). Cubic planar
graphs have maximum degree `3`, so those reductions land in this class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev VertexCoverPlanarMaxDegreeThreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : VertexCoverPlanarMaxDegreeThreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is planar with every vertex degree at most `3`, and `0 < K ≤ |V|`. -/
def WellFormed (i : VertexCoverPlanarMaxDegreeThreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsPlanar ∧ (∀ v, (Graph i).degree v ≤ 3) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at most `K` vertices is a vertex cover of `G`. -/
def VertexCoverPlanarMaxDegreeThreeFeasible (i : VertexCoverPlanarMaxDegreeThreeInstance) :
    Prop :=
  ∃ s : Finset (Fin i.1), s.card ≤ i.2.2 ∧ (Graph i).IsVertexCover (s : Set (Fin i.1))

open Classical in
/-- VERTEX COVER on planar graphs of maximum degree 3 as a decision problem over bitstrings. -/
noncomputable def vertexCoverPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := VertexCoverPlanarMaxDegreeThreeInstance) x with
  | some i => decide (WellFormed i ∧ VertexCoverPlanarMaxDegreeThreeFeasible i)
  | none => false

/-- **VERTEX COVER on planar graphs of maximum degree 3 is NP-complete.** Source: Garey and
Johnson (1979), [GT1] and [GT20], comments; Garey, Johnson and Stockmeyer (1976); Mohar (2001),
Theorem 4.1(a). -/
public theorem_wanted vertexCoverPlanarMaxDegreeThree_npComplete :
    vertexCoverPlanarMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L vertexCoverPlanarMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.VertexCoverPlanarMaxDegreeThree
