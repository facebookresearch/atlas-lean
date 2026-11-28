/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREE ALIGNMENT (given phylogeny, unit metric) is NP-complete

Source:
I. Elias, "Settling the intractability of multiple alignment", Journal of Computational Biology
13(7) (2006), 1323-1339, doi:10.1089/cmb.2006.13.1323.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TreeAlignmentUnitMetricDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeAlignmentUnitMetric

/-!
# TREE ALIGNMENT (given phylogeny, unit metric) is NP-complete

INSTANCE: a finite alphabet `Σ`, a rooted binary tree `T` (the phylogeny) whose `k` leaves are
labelled by strings over `Σ`, and an integer `K`. QUESTION: can the `k - 1` internal vertices
of `T` be labelled by strings over `Σ` so that the sum, over the edges `{u, v}` of `T`, of the
edit distance between the labels of `u` and `v` is at most `K`?

The edit distance is the unit metric: the cost of an optimal pairwise alignment when a
substitution of distinct letters, an insertion and a deletion each cost `1`, that is, CSLib's
unit-cost Levenshtein distance `(Cslib.Algorithms.Lean.editDistance x y).ret.distance`. Elias
(2006) proves TREE ALIGNMENT for a given phylogeny NP-hard for every metric over binary or
larger alphabets, in particular for the unit metric. Membership in NP: in an optimal labelling,
a column of the induced multiple alignment in which every leaf has a gap can be deleted without
raising the cost, so some optimal labelling has internal labels no longer than the total length
of the leaf labels.

Representation: the alphabet is `Σ = {0, ..., |Σ| - 1}` with `|Σ| ≥ 2`, and strings are lists
of letters. The tree has vertices `0, ..., n - 1` with `n = p.length + 1`, root `0`, and is
given by a parent list `p`: vertex `v + 1` is a child of vertex `p[v] ≤ v`. Every rooted tree
has such a list (number its vertices in breadth-first order from the root), and every such list
is a rooted tree. The phylogeny is binary, as in Elias's formulation (`k` leaves and `k - 1`
internal labels): every vertex has no child (a leaf) or exactly two children. The leaf
labelling is a list of (vertex, string) pairs naming every leaf exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TREE ALIGNMENT (given phylogeny, unit metric) is NP-complete.** Source: Elias (2006). -/
public theorem_wanted treeAlignmentUnitMetric_npComplete :
    treeAlignmentUnitMetricDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treeAlignmentUnitMetricDec

end MetaMathlibExt.Complexity.NPComplete.TreeAlignmentUnitMetric
