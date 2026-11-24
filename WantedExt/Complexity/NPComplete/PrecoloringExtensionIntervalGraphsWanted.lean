/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECOLORING EXTENSION ON INTERVAL GRAPHS is NP-complete

Source:
M. Biró, M. Hujter, and Zs. Tuza, "Precoloring extension. I. Interval graphs", Discrete
Mathematics 100(1-3) (1992), 267-279, doi:10.1016/0012-365X(92)90646-W;
D. Marx, *Graph Coloring with Local and Global Constraints*, Ph.D. thesis, Budapest University
of Technology and Economics (2004), Chapter 3 (records the result of Biró, Hujter, and Tuza).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import WantedExt.Complexity.NPComplete.IntervalGraphCompletionWanted
public import WantedExt.Complexity.NPComplete.PrecoloringExtensionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecoloringExtensionIntervalGraphs

open MetaMathlibExt.Complexity.NPComplete.PrecoloringExtension (PrecoloringExtensionInstance)
open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion (IsIntervalGraph)

/-!
# PRECOLORING EXTENSION ON INTERVAL GRAPHS is NP-complete

INSTANCE: an interval graph `G = (V, E)`, a positive integer `K`, and a partial proper coloring
of a set `W ⊆ V` with colors `1, …, K`.
QUESTION: can the partial coloring be extended to a proper `K`-coloring of `G`?

This is PRECOLORING EXTENSION (`PrecoloringExtensionWanted`) restricted to interval graphs. The
instance and the question are those of `PrecoloringExtensionWanted`, reused unchanged: vertex
count `n`, edge list on `Fin n`, a list `pre` of length `n` with `pre[v] = 0` for an uncolored
vertex and `pre[v] = j ≥ 1` for a vertex of `W` precolored with color `j`, and the number of
colors `K`; `PrecoloringExtension.PrecoloringExtensionFeasible` asks for a proper coloring with
colors `0, …, K - 1` that gives every precolored vertex `v` the color `pre[v] - 1` (so the
source's color `j ∈ {1, …, K}` is the parent's color `j - 1`).

The restriction adds to well-formedness what the source puts in the instance class: the graph
`Cslib.Complexity.Karp.edgeGraph n E` is an interval graph (the repository's
`IntervalGraphCompletion.IsIntervalGraph`: closed real intervals, one per vertex, two distinct
vertices adjacent exactly when their intervals meet), `K` is positive, every precolor is one of
`1, …, K`, and the precoloring is proper (no edge joins two vertices precolored alike).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed PRECOLORING EXTENSION instance whose graph is
an interval graph, with `0 < K`, every precolor at most `K`, and no edge joining two vertices
with the same precolor. -/
def WellFormed (i : PrecoloringExtensionInstance) : Prop :=
  PrecoloringExtension.WellFormed i ∧
    IsIntervalGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2.2 ∧
    (∀ v < i.1, i.2.2.1.getD v 0 ≤ i.2.2.2) ∧
    ∀ e ∈ i.2.1, i.2.2.1.getD e.1 0 ≠ 0 → i.2.2.1.getD e.1 0 ≠ i.2.2.1.getD e.2 0

open Classical in
/-- PRECOLORING EXTENSION ON INTERVAL GRAPHS as a decision problem over bitstrings. -/
noncomputable def precoloringExtensionIntervalGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PrecoloringExtensionInstance) x with
  | some i => decide (WellFormed i ∧ PrecoloringExtension.PrecoloringExtensionFeasible i)
  | none => false

/-- **PRECOLORING EXTENSION ON INTERVAL GRAPHS is NP-complete.** Source: Biró, Hujter, and Tuza
(1992). -/
public theorem_wanted precoloringExtensionIntervalGraphs_npComplete :
    precoloringExtensionIntervalGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precoloringExtensionIntervalGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PrecoloringExtensionIntervalGraphs
