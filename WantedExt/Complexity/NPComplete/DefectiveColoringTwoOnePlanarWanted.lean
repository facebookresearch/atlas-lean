/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# (2,1)-DEFECTIVE COLORING of planar graphs is NP-complete

Source:
L. J. Cowen, W. Goddard and C. E. Jesurum, "Defective coloring revisited", Journal of Graph
Theory 24(3) (1997), 205-219, doi:10.1002/(SICI)1097-0118(199703)24:3<205::AID-JGT2>3.0.CO;2-T
(abstract: "the (2, 1)-coloring and the (3, 1)-coloring problems are NP-complete even for
planar graphs").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DefectiveColoringTwoOnePlanar

/-!
# (2,1)-DEFECTIVE COLORING of planar graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)`.
QUESTION: is `G` `(2, 1)`-colorable, i.e. can the vertices be colored with `2` colors so that no
vertex is adjacent to more than `1` vertex of its own color? Equivalently, each color class
induces a subgraph of maximum degree at most `1`.

Cowen, Goddard and Jesurum call a graph `(k, d)`-colorable if its vertices can be colored with
`k` colors such that no vertex is adjacent to more than `d` vertices of its same color, and show
that deciding `(2, 1)`-colorability is NP-complete for planar graphs. Here `k = 2`, `d = 1`: a
coloring is a map `c : Fin n → Fin 2`, and for each vertex `v` the neighbors `u` of `v` (Mathlib's
`SimpleGraph.neighborFinset`) with `c u = c v` number at most `1`.

The graph is given, as in the sibling modules, by a vertex count `n` (vertices `Fin n`) and a
simple edge list, read as `Cslib.Complexity.Karp.edgeGraph`; planarity is MathlibExt's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem exists
exactly for planar graphs). Membership in NP: the certificate is the coloring, and planarity is
decidable in linear time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev DefectiveColoringTwoOnePlanarInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : DefectiveColoringTwoOnePlanarInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, and the
graph is planar. -/
def WellFormed (i : DefectiveColoringTwoOnePlanarInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsPlanar

open Classical in
/-- The graph is `(2, 1)`-colorable: some coloring `c` with `2` colors gives every vertex at
most `1` neighbor of its own color. -/
def DefectiveColoringTwoOnePlanarFeasible (i : DefectiveColoringTwoOnePlanarInstance) : Prop :=
  ∃ c : Fin i.1 → Fin 2, ∀ v : Fin i.1,
    (((Graph i).neighborFinset v).filter fun u => c u = c v).card ≤ 1

open Classical in
/-- (2,1)-DEFECTIVE COLORING of planar graphs as a decision problem over bitstrings. -/
noncomputable def defectiveColoringTwoOnePlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DefectiveColoringTwoOnePlanarInstance) x with
  | some i => decide (WellFormed i ∧ DefectiveColoringTwoOnePlanarFeasible i)
  | none => false

/-- **(2,1)-DEFECTIVE COLORING of planar graphs is NP-complete.** Source: Cowen, Goddard and
Jesurum (1997). -/
public theorem_wanted defectiveColoringTwoOnePlanar_npComplete :
    defectiveColoringTwoOnePlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L defectiveColoringTwoOnePlanarDec

end MetaMathlibExt.Complexity.NPComplete.DefectiveColoringTwoOnePlanar
