/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (crossing, crossing) is NP-complete

Source:
P. A. Evans, "Finding common subsequences with arcs and pseudoknots", Combinatorial Pattern
Matching (CPM 1999), Lecture Notes in Computer Science 1645 (1999), 270-280,
doi:10.1007/3-540-48452-3_20 (full text not available);
G.-H. Lin, Z.-Z. Chen, T. Jiang and J. Wen, "The longest common subsequence problem for
sequences with nested arc annotations", Journal of Computer and System Sciences 65 (2002),
465-480, doi:10.1016/S0022-0000(02)00004-1;
problem definitions as in V. Yu. Popov, "Arc-preserving subsequences of arc-annotated
sequences", Acta Universitatis Sapientiae, Informatica 3 (2011), 35-47, arXiv:1104.4433.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceCrossingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceCrossing

open MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNested
  (LongestArcPreservingCommonSubsequenceNestedInstance
    LongestArcPreservingCommonSubsequenceNestedFeasible)

/-!
# LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (crossing, crossing) is NP-complete

Arc-annotated sequences, common subsequences and arc preservation are as in
`WantedExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceNestedWanted`. Popov's
levels of arc structure: an arc set is crossing if no two arcs share an endpoint, that is, for
all `(i₁, i₂), (i₃, i₄) ∈ P`, `i₁ ≠ i₄`, `i₂ ≠ i₃`, and `i₁ = i₃ ⇔ i₂ = i₄` (every position
lies in at most one arc); arcs may cross (pseudoknots). Nested arc sets are the crossing arc
sets in which, in addition, no two arcs cross.

LAPCS(CROSSING, CROSSING): given two arc-annotated sequences `(S₁, P₁)` and `(S₂, P₂)` with
crossing arc sets and a positive integer `k`, is there a common subsequence `T` of `S₁` and
`S₂` that is arc-preserving with `|T| ≥ k`?

Evans (1999) introduced the problem for arcs with pseudoknots. Every nested arc set is a
crossing arc set, so LAPCS(NESTED, NESTED), proved NP-hard by Lin, Chen, Jiang and Wen (2002)
(`LongestArcPreservingCommonSubsequenceNestedWanted`), is a restriction of this problem with the
same instances and question; NP-hardness follows. It is in NP: the two position mappings are a
certificate. The instance encoding and the question are those of the nested module.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LONGEST ARC-PRESERVING COMMON SUBSEQUENCE (crossing, crossing) is NP-complete.** Source:
Evans (1999); Lin, Chen, Jiang and Wen (2002). -/
public theorem_wanted longestArcPreservingCommonSubsequenceCrossing_npComplete :
    longestArcPreservingCommonSubsequenceCrossingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestArcPreservingCommonSubsequenceCrossingDec

end MetaMathlibExt.Complexity.NPComplete.LongestArcPreservingCommonSubsequenceCrossing
