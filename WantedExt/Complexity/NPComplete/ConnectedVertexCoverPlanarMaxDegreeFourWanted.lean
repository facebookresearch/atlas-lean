/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED VERTEX COVER on planar graphs of maximum degree 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT1] VERTEX COVER, p. 190, comment:
"Variation in which the subgraph induced by V' is required to be connected is also
NP-complete, even for planar graphs with no vertex degree exceeding 4 [Garey and Johnson,
1977a]";
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32(4) (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedVertexCoverPlanarMaxDegreeFour

/-!
# CONNECTED VERTEX COVER on planar graphs of maximum degree 4 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with no vertex degree exceeding `4`, and a positive integer
`K ≤ |V|`.
QUESTION: is there a vertex cover `V'` of size `K` or less for `G` (a subset `V' ⊆ V` with
`|V'| ≤ K` such that for each edge `{u, v} ∈ E` at least one of `u` and `v` belongs to `V'`)
such that the subgraph of `G` induced by `V'` is connected?

The vertex cover is Mathlib's `SimpleGraph.IsVertexCover` of a `Finset` coerced to a set, the
induced subgraph is Mathlib's `SimpleGraph.induce`, and connectedness is Mathlib's
`SimpleGraph.Connected` (nonempty, and any two vertices joined by a walk). Planarity is the
repository's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's
theorem exists exactly for planar graphs) and the degree bound uses Mathlib's
`SimpleGraph.degree`. The graph is given by a vertex count `n` (vertices `Fin n`) and a simple
edge list. Since `K ≥ 1`, requiring `V'` nonempty changes no answer: an edgeless graph has the
one-vertex connected cover.

Membership in NP: the certificate is `V'`; the cover, connectivity and degree conditions are
checked directly and planarity in linear time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568).

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
abbrev ConnectedVertexCoverPlanarMaxDegreeFourInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ConnectedVertexCoverPlanarMaxDegreeFourInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, the graph
is planar with every vertex degree at most `4`, and `0 < K ≤ |V|`. -/
def WellFormed (i : ConnectedVertexCoverPlanarMaxDegreeFourInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsPlanar ∧ (∀ v, (Graph i).degree v ≤ 4) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at most `K` vertices is a vertex cover of `G` inducing a connected subgraph. -/
def ConnectedVertexCoverPlanarMaxDegreeFourFeasible
    (i : ConnectedVertexCoverPlanarMaxDegreeFourInstance) : Prop :=
  ∃ s : Finset (Fin i.1), s.card ≤ i.2.2 ∧ (Graph i).IsVertexCover (s : Set (Fin i.1)) ∧
    ((Graph i).induce (s : Set (Fin i.1))).Connected

open Classical in
/-- CONNECTED VERTEX COVER on planar graphs of maximum degree 4 as a decision problem over
bitstrings. -/
noncomputable def connectedVertexCoverPlanarMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConnectedVertexCoverPlanarMaxDegreeFourInstance) x with
  | some i => decide (WellFormed i ∧ ConnectedVertexCoverPlanarMaxDegreeFourFeasible i)
  | none => false

/-- **CONNECTED VERTEX COVER on planar graphs of maximum degree 4 is NP-complete.** Source:
Garey and Johnson (1979), [GT1], comment; Garey and Johnson (1977). -/
public theorem_wanted connectedVertexCoverPlanarMaxDegreeFour_npComplete :
    connectedVertexCoverPlanarMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedVertexCoverPlanarMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedVertexCoverPlanarMaxDegreeFour
