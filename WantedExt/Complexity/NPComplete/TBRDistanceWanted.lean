/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TBR DISTANCE is NP-complete

Source:
B. L. Allen and M. Steel, "Subtree transfer operations and their induced metrics on
evolutionary trees", Annals of Combinatorics 5 (2001), 1-15, doi:10.1007/s00026-001-8006-8;
J. Hein, T. Jiang, L. Wang and K. Zhang, "On the complexity of comparing evolutionary trees",
Discrete Applied Mathematics 71 (1996), 153-169, doi:10.1016/S0166-218X(96)00062-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TBRDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TBRDistance

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits

/-!
# TBR DISTANCE is NP-complete

INSTANCE: two unrooted binary phylogenetic trees `T₁`, `T₂` on the same taxon set `X` with
`|X| ≥ 3`, and a natural number `K`. QUESTION: is the tree-bisection-and-reconnection distance `d_TBR(T₁, T₂)` at
most `K`, that is, is there an agreement forest for `T₁`, `T₂` with at most `K + 1` trees?

Trees are the repository's unrooted binary phylogenetic trees (`UnrootedBinaryTree`: a finite
tree whose leaves, the vertices of degree 1, are labeled bijectively by `X`, every other vertex
having degree 3; Allen and Steel, Definition 1.1). The taxa are `X = Fin m`. A tree is given by
its number of vertices `n`, its edge list on `Fin n`, and the list whose `x`-th entry is the
leaf of taxon `x` (`TreeData`); `IsPhyloTree m t` says that the data describe such a tree, and
`toTree` is that tree.

An agreement forest (Allen and Steel, Definition 2.12) is a partition `L₁, …, L_k` of `X` such
that (2) `T₁|Lⱼ = T₂|Lⱼ` for every `j`, and (3) for `i = 1, 2` the minimal subtrees `Tᵢ(Lⱼ)`
of `Tᵢ` connecting the leaves of `Lⱼ` are vertex-disjoint. The partition is a Mathlib
`Finpartition` of `Finset.univ`; the vertices of `T(L)` are the vertices on the path between two
leaves of `L` (`spanVerts`). Condition (2) is stated with quartets (`DisplaysQuartet T a b c d`,
the quartet `ab|cd`): for any four distinct taxa of `Lⱼ`, `T₁` displays `ab|cd` iff `T₂` does.
This is equivalent to (2): for `a, b, c, d ∈ L`, `T|L` displays `ab|cd` iff `T` does, since
the paths between `a, b` and between `c, d` lie in `T(L)` and forced contractions do not change
whether they share a vertex; isomorphic trees display the same quartets; and an unrooted binary
tree is determined up to isomorphism by its quartets (Semple and Steel 2003, Corollary 6.3.8;
`iso_of_displaysQuartet_iff`). When `|Lⱼ| ≤ 3` there is a single tree on `Lⱼ` and no four
distinct taxa.

Allen and Steel, Theorem 2.13, give `d_TBR(T₁, T₂) = m(T₁, T₂)`, the least number of trees of an
agreement forest minus 1, so `d_TBR(T₁, T₂) ≤ K` iff some agreement forest has at most `K + 1`
trees. They state (Section 3) that the proof of Theorem 8 of Hein, Jiang, Wang and Zhang
(NP-hardness of the maximum agreement forest problem) establishes that the TBR-distance problem
is NP-hard. Membership in NP: an agreement forest is a polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TBR DISTANCE is NP-complete.** Source: Allen and Steel (2001), Theorem 2.13 and
Section 3; Hein, Jiang, Wang and Zhang (1996), Theorem 8. -/
public theorem_wanted tbrDistance_npComplete :
    tbrDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tbrDistanceDec

end MetaMathlibExt.Complexity.NPComplete.TBRDistance
