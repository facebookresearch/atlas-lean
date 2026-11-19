/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET ON SPLIT GRAPHS is NP-complete

Source:
K. White, M. Farber and W. Pulleyblank, "Steiner trees, connected domination and strongly
chordal graphs", Networks 15 (1985), 109-124, doi:10.1002/net.3230150109;
A. Mohanapriya, P. Renjith and N. Sadagopan, "On convexity in split graphs: complexity of
Steiner tree and domination", Journal of Combinatorial Optimization 47 (2024), no. 2,
article 8, doi:10.1007/s10878-024-01105-1 (arXiv:2210.02288, Section 3, "Application 4:
Domination and its variants").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Domination

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SplitConnectedDominatingSet

/-!
# CONNECTED DOMINATING SET ON SPLIT GRAPHS is NP-complete

INSTANCE: a split graph `G = (V, E)`, that is, a graph whose vertex set can be partitioned into
a clique and an independent set, and a positive integer `K`. QUESTION: is there a dominating
set `V' ⊆ V` with `|V'| ≤ K` such that the induced subgraph `G[V']` is connected?

The split condition is part of the instance class, so it is a conjunct of `WellFormed`: some
vertex set `C` is a clique (`SimpleGraph.IsClique`) whose complement is an independent set
(`SimpleGraph.IsIndepSet`). Domination is the shared `SimpleGraph.IsDominating`, and
connectivity of `G[V']` is Mathlib's `SimpleGraph.Connected` of `G.induce V'`, which also makes
`V'` nonempty.

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
abbrev SplitConnectedDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : SplitConnectedDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is a split
graph (some vertex set `C` is a clique and its complement is an independent set), and `0 < K`. -/
def WellFormed (i : SplitConnectedDominatingSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∃ C : Set (Fin i.1), (Graph i).IsClique C ∧ (Graph i).IsIndepSet Cᶜ) ∧
    0 < i.2.2

/-- Some dominating set `V'` of at most `K` vertices induces a connected subgraph. -/
def SplitConnectedDominatingSetFeasible (i : SplitConnectedDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ (Graph i).IsDominating (↑S : Set (Fin i.1)) ∧
    ((Graph i).induce (↑S : Set (Fin i.1))).Connected

open Classical in
/-- CONNECTED DOMINATING SET ON SPLIT GRAPHS as a decision problem over bitstrings. -/
noncomputable def splitConnectedDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SplitConnectedDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ SplitConnectedDominatingSetFeasible i)
  | none => false

/-- **CONNECTED DOMINATING SET ON SPLIT GRAPHS is NP-complete.** Source: White, Farber and
Pulleyblank (1985); Mohanapriya, Renjith and Sadagopan (2024). -/
public theorem_wanted splitConnectedDominatingSet_npComplete :
    splitConnectedDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L splitConnectedDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.SplitConnectedDominatingSet
