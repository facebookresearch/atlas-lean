/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CHORDAL GRAPHS is NP-complete

Source:
J. Gustedt, "On the pathwidth of chordal graphs", Discrete Applied Mathematics 45(3) (1993),
233-248, doi:10.1016/0166-218X(93)90012-D.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs

/-!
# PATHWIDTH OF CHORDAL GRAPHS is NP-complete

INSTANCE: a chordal graph `G = (V, E)` (every cycle of length at least `4` has a chord) and a
positive integer `K`.
QUESTION: does `G` have pathwidth at most `K`?

A path decomposition of `G` is a sequence of bags `X 0, …, X (r - 1)` of vertices such that every
vertex lies in some bag, both ends of every edge lie in a common bag, and the bags containing any
one vertex are consecutive (`IsPathDecomposition`). Its width is the largest bag size minus one,
and the pathwidth of `G` is the least width of a path decomposition; so the pathwidth is at most
`K` exactly when some path decomposition has all bags of size at most `K + 1`. (Equivalently, `G`
is a subgraph of an interval graph with clique number at most `K + 1`.)

Chordality is part of the instance class, so it is a conjunct of `WellFormed`: no cycle graph `Cₖ`
with `k ≥ 4` is an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and
`SimpleGraph.IsIndContained`; a cycle has a chord exactly when its vertices do not induce a cycle
graph). As in the source, `K` is positive.

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
abbrev PathwidthChordalGraphsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PathwidthChordalGraphsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is chordal
(no induced cycle of length at least `4`), and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)) ∧ 0 < i.2.2

/-- The bags `X 0, …, X (r - 1)` form a path decomposition of `G`: every vertex is in some bag,
both ends of every edge are in a common bag, and every vertex in bags `X t₁` and `X t₃` is in
every bag `X t₂` between them. -/
def IsPathDecomposition {n r : ℕ} (G : SimpleGraph (Fin n)) (X : Fin r → Finset (Fin n)) :
    Prop :=
  (∀ v, ∃ t, v ∈ X t) ∧ (∀ u v, G.Adj u v → ∃ t, u ∈ X t ∧ v ∈ X t) ∧
    ∀ v t₁ t₂ t₃, t₁ ≤ t₂ → t₂ ≤ t₃ → v ∈ X t₁ → v ∈ X t₃ → v ∈ X t₂

/-- The graph has pathwidth at most `K`: some path decomposition has every bag of size at most
`K + 1`. -/
def PathwidthChordalGraphsFeasible (i : PathwidthChordalGraphsInstance) : Prop :=
  ∃ r : ℕ, ∃ X : Fin r → Finset (Fin i.1), IsPathDecomposition (Graph i) X ∧
    ∀ t, (X t).card ≤ i.2.2 + 1

open Classical in
/-- PATHWIDTH OF CHORDAL GRAPHS as a decision problem over bitstrings. -/
noncomputable def pathwidthChordalGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphsFeasible i)
  | none => false

/-- **PATHWIDTH OF CHORDAL GRAPHS is NP-complete.** Source: Gustedt (1993). -/
public theorem_wanted pathwidthChordalGraphs_npComplete :
    pathwidthChordalGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthChordalGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
