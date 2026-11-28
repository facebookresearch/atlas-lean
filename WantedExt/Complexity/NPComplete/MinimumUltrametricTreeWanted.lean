/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM ULTRAMETRIC TREE is NP-complete

Source:
B. Y. Wu, K.-M. Chao and C. Y. Tang, "Approximation and exact algorithms for constructing
minimum ultrametric trees from distance matrices", Journal of Combinatorial Optimization 3
(1999), 199-211, doi:10.1023/A:1009885610075 (the minimum ultrametric tree problem is NP-hard,
also when the distance matrix is a metric);
M. Křivánek and J. Morávek, "NP-hard problems in hierarchical-tree clustering", Acta
Informatica 23 (1986), 311-323, doi:10.1007/BF00289116.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumUltrametricTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumUltrametricTree

open Cslib.Bioinformatics.Phylogenetics.Splits (IsHierarchy)

/-!
# MINIMUM ULTRAMETRIC TREE is NP-complete

INSTANCE: an `n × n` metric distance matrix `M` on `n ≥ 1` species, with nonnegative integer
entries, and an integer `K`.
QUESTION: is there an ultrametric tree for `M` of total edge weight at most `K`, i.e. a rooted
tree with nonnegative edge weights whose leaves are the species, in which all leaves are at the
same distance from the root and the path distance `d_T(i, j)` between any two leaves is at least
`M[i, j]`?

This is the metric version (MMUT) of the minimum ultrametric tree problem; Wu, Chao and Tang
(1999) show that both the general version and the metric version are NP-hard.

The species are `Fin n`, the matrix is the list of its `n` rows, and the metric conditions are
zero diagonal, positive and symmetric off-diagonal entries, and the triangle inequality. A tree is
given as a *dated hierarchy*, the encoding of `Cslib.Bioinformatics.Phylogenetics.Splits`'
`IsDatedTreeMetric`: its clusters (the leaf sets below its vertices) form a hierarchy `H` on the
species (`IsHierarchy`), and each cluster `C` carries a date `h C`, `0` at the leaves and
strictly increasing from a cluster to any cluster strictly containing it. The edge from a cluster
`C` other than the root to its parent `par C` (the smallest cluster strictly containing `C`) has
weight `(h (par C) - h C) / 2`, all leaves are at distance `h univ / 2` from the root, and the
path distance between distinct leaves `i, j` is the date of the smallest cluster containing both.
Every ultrametric tree for `M` arises this way after contracting internal edges of weight `0` and
suppressing vertices with one child, which changes neither the leaf distances nor the total
weight; its leaf edges have positive weight, since distinct species are at distance
`d_T(i, j) ≥ M[i, j] > 0`. For membership in NP: for a fixed hierarchy with dates allowed to be
equal, the total weight is nondecreasing in every internal date (each internal cluster has at least
two children), so the least admissible dates `h C = max_{i, j ∈ C} M[i, j]` are optimal, and
merging clusters with equal dates then gives a strictly dated hierarchy with the same distances and
weight. Optimal trees therefore have integer dates. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM ULTRAMETRIC TREE is NP-complete.** Source: Wu, Chao and Tang (1999). -/
public theorem_wanted minimumUltrametricTree_npComplete :
    minimumUltrametricTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumUltrametricTreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumUltrametricTree
