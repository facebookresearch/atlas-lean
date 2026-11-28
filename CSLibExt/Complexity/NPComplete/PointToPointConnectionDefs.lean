/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

/-!
# POINT-TO-POINT CONNECTION: definitions

INSTANCE: a graph `G = (V, E)`, a weight function `w : E → ℕ`, sources `s₁, …, s_p` and
destinations `d₁, …, d_p`, and a positive integer `K`.
QUESTION: is there a point-to-point connection, that is, a subset `E' ⊆ E` such that each
source-destination pair `(sⱼ, dⱼ)` is connected by a path using only edges of `E'`, with
`∑_{e ∈ E'} w(e) ≤ K`?

This is the fixed-destination, undirected version (`C/f/u`) of the point-to-point connection
problem of Li, McCormick and Simchi-Levi (1992): "find a subset of arcs `A' ⊆ A` such that each
source-destination pair is connected by a path using only arcs in `A'`", with non-negative
integral costs; they prove all four versions strongly NP-hard. As in their definition, the
sources and destinations need not be distinct vertices. The vertices are `0, ..., n - 1`; the
graph is given by a simple edge list whose entries `(u, v, w)` carry the weight of the edge
`{u, v}`, and the pairs `(sⱼ, dⱼ)` are listed. A subset `E'` is a sublist of the edge list
(the list has no repeated edges); its graph is `Cslib.Complexity.Karp.edgeGraph` of its
endpoints, and "connected by a path" is `SimpleGraph.Reachable` in that graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), section Graph Theory, problem MINIMUM POINT-TO-POINT CONNECTION (decision version);
C.-L. Li, S. T. McCormick and D. Simchi-Levi, "The point-to-point delivery and connection
problems: complexity and algorithms", Discrete Appl. Math. 36 (1992), 267-292,
doi:10.1016/0166-218X(92)90258-C, Section 2 (definition) and Section 3 (all four point-to-point
connection problems are strongly NP-hard).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PointToPointConnection

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list with weights
`(u, v, w(u, v))`, the source-destination pairs `(sⱼ, dⱼ)`, and `K`. -/
abbrev PointToPointConnectionInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every source and
destination is a vertex, and `K` is positive. -/
def WellFormed (i : PointToPointConnectionInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (∀ q ∈ i.2.2.1, q.1 < i.1 ∧ q.2 < i.1) ∧ 0 < i.2.2.2

/-- Some sublist of edges has total weight at most `K` and connects the source to the
destination of each pair whose endpoints are both in range. A pair with an out-of-range
endpoint imposes no connectivity requirement. `WellFormed` requires every endpoint in range. -/
def PointToPointConnectionFeasible (i : PointToPointConnectionInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ × ℕ), E'.Sublist i.2.1 ∧ (E'.map fun e => e.2.2).sum ≤ i.2.2.2 ∧
    ∀ q ∈ i.2.2.1, ∀ (hs : q.1 < i.1) (hd : q.2 < i.1),
      (Cslib.Complexity.Karp.edgeGraph i.1 (E'.map fun e => (e.1, e.2.1))).Reachable
        ⟨q.1, hs⟩ ⟨q.2, hd⟩

open Classical in
/-- POINT-TO-POINT CONNECTION as a decision problem over bitstrings. -/
noncomputable def pointToPointConnectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PointToPointConnectionInstance) x with
  | some i => decide (WellFormed i ∧ PointToPointConnectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PointToPointConnection
