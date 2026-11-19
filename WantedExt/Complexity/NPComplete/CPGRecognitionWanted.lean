/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF CPG GRAPHS is NP-complete

Source:
N. Champseix, E. Galby, A. Munaro and B. Ries, "CPG graphs: Some structural and hardness
results", Discrete Applied Mathematics 290 (2021), 17-35, doi:10.1016/j.dam.2020.11.018,
Theorem 10 ("Recognition is NP-complete in CPG"; membership in NP is their Theorem 4);
Z. Deniz, E. Galby, A. Munaro and B. Ries, "On contact graphs of paths on a grid", Graph Drawing
2018, LNCS 11282 (2018), 317-330, doi:10.1007/978-3-030-04414-5_22 (the class).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CPGRecognition

/-!
# RECOGNITION OF CPG GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a CPG graph (ISGCI `gc_1336`)? In the words of
Champseix, Galby, Munaro and Ries (2021): "a graph `G = (V, E)` is a CPG graph if there exists a
collection `P` of pairwise interiorly disjoint paths on a grid `G` in one-to-one correspondence
with `V` such that two vertices are adjacent if and only if the corresponding paths touch", where
"an interior point of a path `P` is a point belonging to `P` and different from its endpoints"
and paths "touch if `P` and `P'` have a common grid-point". Their Theorem 10 proves recognition
NP-complete; membership in NP is their Theorem 4 (every CPG graph on `n` vertices has a CPG
representation on a grid of area `O(n²)`).

The graph is given by an edge list on `Fin n`. A path on a grid is a path
(`SimpleGraph.Walk.IsPath`) of the `N × N` grid graph `grid N` (Mathlib's box product of two
`SimpleGraph.pathGraph N`; grid points are `Fin N × Fin N`, adjacent when they differ by `1` in
one coordinate), for some `N`; every finite representation fits in such a grid after a
translation. As in the sources (each path has two endpoints, and the merged
`PartitionIntoCliquesBZeroCPGWanted` asks for segments of positive length), a path has at least one
grid edge. Two such paths have a common point in the plane exactly when they have a common grid
point (a common non-grid point lies on a common grid edge), and a common interior point exactly
when they have a common grid edge (whose midpoint is interior to both) or a common grid point that
is interior to both; so "interiorly disjoint" is: no common grid edge, and every common grid point
is an endpoint of one of the two paths.

Membership in NP: isolated vertices do not change the answer (each is a unit path in fresh rows
beyond the representation of the rest), so the certificate is a representation of the subgraph
on the vertices that occur in edges, on a grid of area `O(n²)` (Theorem 4), and the binary vertex
count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev CPGRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CPGRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CPGRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The `N × N` grid graph: grid points `Fin N × Fin N`, two of them adjacent when they differ by
`1` in one coordinate and agree in the other. -/
abbrev grid (N : ℕ) : SimpleGraph (Fin N × Fin N) :=
  SimpleGraph.pathGraph N □ SimpleGraph.pathGraph N

/-- `P` is a CPG representation of `G` on the `N × N` grid: every `P v` (a walk of the grid from
`a v` to `b v`) is a path with at least one grid edge; two distinct paths have no common grid edge,
and every common grid point is an endpoint of one of them (they are interiorly disjoint); and two
distinct vertices are adjacent if and only if their paths have a common grid point (touch). -/
def IsCPGRepresentation {V : Type*} (G : SimpleGraph V) (N : ℕ) (a b : V → Fin N × Fin N)
    (P : ∀ v, (grid N).Walk (a v) (b v)) : Prop :=
  (∀ v, (P v).IsPath ∧ 0 < (P v).length) ∧
    (∀ u v, u ≠ v → (∀ e, e ∈ (P u).edges → e ∉ (P v).edges) ∧
      ∀ x, x ∈ (P u).support → x ∈ (P v).support → x = a u ∨ x = b u ∨ x = a v ∨ x = b v) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ ∃ x, x ∈ (P u).support ∧ x ∈ (P v).support)

/-- The graph of the instance is a CPG graph: it has a CPG representation on some grid. -/
def CPGRecognitionFeasible (i : CPGRecognitionInstance) : Prop :=
  ∃ (N : ℕ) (a b : Fin i.1 → Fin N × Fin N) (P : ∀ v, (grid N).Walk (a v) (b v)),
    IsCPGRepresentation (Graph i) N a b P

open Classical in
/-- RECOGNITION OF CPG GRAPHS as a decision problem over bitstrings. -/
noncomputable def cpgRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CPGRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ CPGRecognitionFeasible i)
  | none => false

/-- **RECOGNITION OF CPG GRAPHS is NP-complete.** Source: Champseix, Galby, Munaro and Ries
(2021), Theorems 4 and 10. -/
public theorem_wanted cpgRecognition_npComplete :
    cpgRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cpgRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.CPGRecognition
