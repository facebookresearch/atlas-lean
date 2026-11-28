/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for K₃,₃-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (comment:
remains NP-complete for `K = 3` and planar graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth edition), Journal of
Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "K3,3-Free",
column "ChrNum": "N [GJ]"), and Section 3 ("K3,3-free Graphs. These are graphs that contain no
subgraphs homeomorphic to K3,3 but may contain ones homeomorphic to K5.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChromaticNumberK33FreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberK33Free

open MetaMathlibExt.Complexity.NPComplete.GraphColoring
  (GraphColoringInstance Graph GraphColoringFeasible)

/-!
# CHROMATIC NUMBER for K₃,₃-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no subgraph homeomorphic to `K₃,₃`, and a positive integer
`K`. QUESTION: is the chromatic number of `G` at most `K`, i.e. is `G` `K`-colorable?

This is GRAPH K-COLORABILITY ([GT4], `GraphColoringWanted`) restricted to `K₃,₃`-free graphs,
the entry of Johnson's Table 1 (sixteenth column) for CHROMATIC NUMBER on that class: planar
graphs contain no subgraph homeomorphic to `K₃,₃`, and Garey and Johnson record that the problem
stays NP-complete for planar graphs. The instance type, `GraphColoring.Graph` and
`GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`, Mathlib's `Colorable`) are the
parent's, unchanged; `WellFormed` keeps the parent's simple-edge-list condition and adds `0 < K`
(as in `ChromaticNumberHFreeGraphsWanted`) and the restriction.

A subgraph homeomorphic to `K₃,₃` (a subdivision of `K₃,₃` inside `G`) is given by six distinct
branch vertices `a₀, a₁, a₂, b₀, b₁, b₂` and nine paths, one from each `aᵢ` to each `bⱼ`, such
that any two of the paths are internally disjoint (MathlibExt
`SimpleGraph.InternallyDisjoint`: no common vertex other than an end) and no path passes
through a branch vertex other than its two ends (`HasK33Subdivision`). Each edge of `K₃,₃`
becomes one of the paths, with the subdivision vertices as its interior.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CHROMATIC NUMBER is NP-complete for `K₃,₃`-free graphs.** Source: Garey and Johnson
(1979), [GT4]; Johnson, NP-completeness column (1985), Table 1. -/
public theorem_wanted chromaticNumberK33Free_npComplete :
    chromaticNumberK33FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticNumberK33FreeDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberK33Free
