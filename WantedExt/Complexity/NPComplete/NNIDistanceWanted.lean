/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NNI DISTANCE is NP-complete

Source:
B. DasGupta, X. He, T. Jiang, M. Li, J. Tromp and L. Zhang, "On computing the nearest neighbor
interchange distance", in *Discrete Mathematical Problems with Medical Applications*, DIMACS
Series in Discrete Mathematics and Theoretical Computer Science 55 (2000), 125-143,
doi:10.1090/dimacs/055/09 (Section 1: nni operations and the nni distance; Theorem 1: "Let `T1`
and `T2` be two trees with unique leaf labels and `k` be an integer. It is NP-complete to decide if
`Dnni(T1, T2) ≤ k`"; conference version in the Proceedings of the Eighth Annual ACM-SIAM Symposium
on Discrete Algorithms (SODA 1997), 427-436).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NNIDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NNIDistance

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open MetaMathlibExt.Complexity.NPComplete.TBRDistance (TreeData IsPhyloTree toTree)

/-!
# NNI DISTANCE is NP-complete

INSTANCE: two unrooted binary phylogenetic trees `T₁`, `T₂` on the same taxon set (internal
vertices of degree 3, leaves labeled bijectively by the taxa), and a natural number `K`.
QUESTION: is the nearest neighbor interchange distance `Dnni(T₁, T₂)` at most `K`?

DasGupta et al. (Section 1): "An nni operation swaps two subtrees that are separated by an
internal edge `(u, v)` ... (An edge `(u, v)` is internal if neither `u` nor `v` is a leaf.) ...
The nni distance, `Dnni(T1, T2)`, between two trees `T1` and `T2` is defined as the minimum number
of nni operations required to transform one tree into the other." Their trees have "all internal
nodes of degree 3 and unique labels on leaves", and "two trees are considered equal iff there is
an isomorphism between them preserving topology ... and leaf labels". Theorem 1 proves the
problem NP-complete by a reduction from EXACT COVER BY 3-SETS.

Trees are the repository's unrooted binary phylogenetic trees (`UnrootedBinaryTree`, with
`UnrootedBinaryTree.Iso` the label-preserving isomorphism), given as in `TBRDistanceWanted` by the
data `TBRDistance.TreeData` (vertex count, edge list, leaf of each taxon), checked by
`TBRDistance.IsPhyloTree` and read by `TBRDistance.toTree`; the taxa are `Fin m`. Let the internal
edge `uv` separate the subtrees `A`, `B` at `u` from `C`, `D` at `v`, rooted at the neighbors
`a`, `b` of `u` and `c`, `d` of `v`. The nni operation exchanging `B` and `C` replaces the edges
`ub` and `vc` by `uc` and `vb` and keeps every vertex and leaf label (`nniSwap`); the other
operation on `uv`, exchanging `B` and `D`, is the same with `d` for `c`. `IsNNIStep T T'` says
that `T'` is, up to label-preserving isomorphism, the result of one nni operation on `T`, and the
distance is at most `K` when a sequence of at most `K` such steps leads from `T₁` to `T₂`, up to
label-preserving isomorphism (`NNIDistanceAtMost`). Membership in NP: `n log n + O(n)` nni
operations suffice between any two trees with `n` leaves (Culik and Wood, as recorded by DasGupta
et al. in the *Handbook of Combinatorial Optimization* (1998), 35-76), so the answer is yes for
larger `K`, and otherwise the sequence of operations is a polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NNI DISTANCE is NP-complete.** Source: DasGupta, He, Jiang, Li, Tromp and Zhang (2000),
Theorem 1. -/
public theorem_wanted nniDistance_npComplete :
    nniDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nniDistanceDec

end MetaMathlibExt.Complexity.NPComplete.NNIDistance
