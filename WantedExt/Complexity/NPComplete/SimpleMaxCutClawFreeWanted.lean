/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for claw-free graphs is NP-complete

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal of
Computing 7(1) (2000), 14-31 (conference version: STACS 94, LNCS 775 (1994), 769-780,
doi:10.1007/3-540-57785-8_189) (NP-complete for "graphs that are the complement of a bipartite
graph", which are claw-free);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021,
Table 1 (MAX CUT on CLAW-FREE: N [20], [20] = Bodlaender and Jansen).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SimpleMaxCutClawFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutClawFree

open MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT for claw-free graphs is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced `K₁,₃`) and a positive integer `K`.
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT restricted to claw-free graphs. Bodlaender and Jansen prove SIMPLE MAX CUT
NP-complete for "graphs that are the complement of a bipartite graph"; such a graph is claw-free
(its vertex set is the union of two cliques, so any three vertices include two adjacent ones),
and the 2022 revision of Johnson's table lists the claw-free entry as NP-complete with this
reference. The instance, the simple-edge-list conditions and the question are those of MAXIMUM
CUT (`MaxCutDefs`, whose question counts edges), reused as in `MaxCutSplitGraphsWanted`; the
restriction adds claw-freeness of `Cslib.Complexity.Karp.edgeGraph` and `0 < K` to `WellFormed`.

Claw-freeness is the repository's predicate `SimpleGraph.IsClawFree` (from
`MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly`, as in `PolarityClawFreeWanted`):
no vertex `c` with three distinct, pairwise non-adjacent neighbours `l₁, l₂, l₃`, i.e. no induced
`K₁,₃`.

Membership in NP holds for all graphs, and claw-freeness is checked in `O(n⁴)` time; isolated
vertices change neither the class nor the answer, so the binary vertex count does not make the
problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SIMPLE MAX CUT for claw-free graphs is NP-complete.**
Source: Bodlaender and Jansen (2000). -/
public theorem_wanted simpleMaxCutClawFree_npComplete :
    simpleMaxCutClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutClawFree
