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
public import CSLibExt.Complexity.NPComplete.PerfectlyOrderableGraphDefs

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

/-- **PERFECTLY ORDERABLE GRAPH RECOGNITION is NP-complete.** Source: Middendorf and Pfeiffer
(1990). -/
public theorem_wanted perfectlyOrderableGraph_npComplete :
    perfectlyOrderableGraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L perfectlyOrderableGraphDec

end MetaMathlibExt.Complexity.NPComplete.PerfectlyOrderableGraph
