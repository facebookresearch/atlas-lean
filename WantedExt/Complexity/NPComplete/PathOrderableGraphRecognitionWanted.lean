/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH ORDERABLE GRAPH RECOGNITION is NP-complete

Source:
D. G. Corneil, E. Köhler, S. Olariu and L. Stewart, "Linear orderings of subfamilies of
AT-free graphs", SIAM Journal on Discrete Mathematics 20 (2006), 105-118,
doi:10.1137/S0895480104445307;
ISGCI (https://www.graphclasses.org/classes/gc_933.html), problem "Recognition" on path
orderable graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Logic.Equiv.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathOrderableGraphRecognition

/-!
# PATH ORDERABLE GRAPH RECOGNITION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` path orderable?

Corneil, Köhler, Olariu and Stewart (2006), Section 1: "We say that a vertex in a graph
`G = (V, E)` intercepts a path in `G` if it is adjacent to at least one vertex of the path, and
it misses the path otherwise." Definition 1.2: "A graph `G = (V, E)` is path orderable if there
is an ordering `v₁, …, vₙ` of the vertices such that for each triple of vertices `vᵢ, vⱼ, v_k`
with `i < j < k` and `vᵢv_k ∉ E`, vertex `vⱼ` intercepts each `vᵢ, v_k`-path of `G`; such an
ordering is called a path ordering." Their abstract: "we settle the recognition question for the
two new classes by proving that recognizing path orderable graphs is NP-complete". (ISGCI's
summary of the definition omits the condition `vᵢv_k ∉ E`; the source's definition is used.)
Membership in NP: a path ordering is a certificate, since `w` intercepts every `u, x`-path
exactly when `u` or `x` is a neighbor of `w`, or `u` and `x` lie in different connected
components of `G` minus the neighbors of `w`.

The ordering is a bijection `pos : Fin n ≃ Fin n` giving each vertex its position. A path is a
Mathlib walk `p : G.Walk u x` with `p.IsPath` (no repeated vertex); `w` intercepts it when `w`
is adjacent to some vertex of `p.support`. The graph is given by an edge list on `Fin n` as in
the other graph statements of this directory (`Cslib.Complexity.Karp.edgeGraph`).

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
abbrev PathOrderableGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PathOrderableGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PathOrderableGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `pos` (vertex ↦ position) is a path ordering of `G`: for every triple `u, w, x` in this
order with `u` and `x` non-adjacent, `w` is adjacent to a vertex of every `u, x`-path. -/
def IsPathOrdering {n : ℕ} (G : SimpleGraph (Fin n)) (pos : Fin n ≃ Fin n) : Prop :=
  ∀ u w x, pos u < pos w → pos w < pos x → ¬ G.Adj u x →
    ∀ p : G.Walk u x, p.IsPath → ∃ y ∈ p.support, G.Adj w y

/-- The graph of the instance is path orderable: it has a path ordering. -/
def PathOrderableGraphRecognitionFeasible (i : PathOrderableGraphRecognitionInstance) : Prop :=
  ∃ pos : Fin i.1 ≃ Fin i.1, IsPathOrdering (Graph i) pos

open Classical in
/-- PATH ORDERABLE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def pathOrderableGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathOrderableGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ PathOrderableGraphRecognitionFeasible i)
  | none => false

/-- **PATH ORDERABLE GRAPH RECOGNITION is NP-complete.** Source: Corneil, Köhler, Olariu and
Stewart (2006). -/
public theorem_wanted pathOrderableGraphRecognition_npComplete :
    pathOrderableGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathOrderableGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.PathOrderableGraphRecognition
