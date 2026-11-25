/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERFECTLY ORDERABLE GRAPH RECOGNITION is NP-complete

Source:
M. Middendorf and F. Pfeiffer, "On the complexity of recognizing perfectly orderable graphs",
Discrete Mathematics 80(3) (1990), 327-333, doi:10.1016/0012-365X(90)90251-C;
V. Chvátal, "Perfectly orderable graphs", in *Topics in Perfect Graphs* (C. Berge and
V. Chvátal, eds.), Annals of Discrete Mathematics 21 (1984), 63-68 (definition and the
obstruction characterization).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PerfectlyOrderableGraph

/-!
# PERFECTLY ORDERABLE GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected).
QUESTION: is `G` perfectly orderable, that is, does `V` have a linear order on which the greedy
coloring algorithm optimally colors every induced subgraph of `G`?

By Chvátal's theorem, a linear order `<` of `V` has this property (is a perfect order) exactly
when it has no obstruction: no four vertices `a, b, c, d` inducing the path `a - b - c - d`
(edges `ab`, `bc`, `cd`; non-edges `ac`, `bd`, `ad`) with `a < b` and `d < c`. The statement
uses this characterization. A linear order of the vertices is given by distinct ranks `rank v`
(`rank` injective; `u` precedes `v` when `rank u < rank v`). The four vertices of an induced
path are automatically distinct: the three edges and three non-edges rule out every
coincidence.

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
abbrev PerfectlyOrderableGraphInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PerfectlyOrderableGraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PerfectlyOrderableGraphInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The vertex order given by the ranks `rank` has no obstruction: no induced path
`a - b - c - d` of `G` has `a` before `b` and `d` before `c`. -/
def IsPerfectOrder {n : ℕ} (G : SimpleGraph (Fin n)) (rank : Fin n → ℕ) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj a c → ¬ G.Adj b d → ¬ G.Adj a d →
    ¬ (rank a < rank b ∧ rank d < rank c)

/-- The graph is perfectly orderable: some linear order of its vertices (distinct ranks) is a
perfect order. -/
def PerfectlyOrderableGraphFeasible (i : PerfectlyOrderableGraphInstance) : Prop :=
  ∃ rank : Fin i.1 → ℕ, Function.Injective rank ∧ IsPerfectOrder (Graph i) rank

open Classical in
/-- PERFECTLY ORDERABLE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def perfectlyOrderableGraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PerfectlyOrderableGraphInstance) x with
  | some i => decide (WellFormed i ∧ PerfectlyOrderableGraphFeasible i)
  | none => false

/-- **PERFECTLY ORDERABLE GRAPH RECOGNITION is NP-complete.** Source: Middendorf and Pfeiffer
(1990). -/
public theorem_wanted perfectlyOrderableGraph_npComplete :
    perfectlyOrderableGraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L perfectlyOrderableGraphDec

end MetaMathlibExt.Complexity.NPComplete.PerfectlyOrderableGraph
