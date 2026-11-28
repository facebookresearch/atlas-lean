/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting) is NP-complete

Source:
M. Křivánek and J. Morávek, "NP-hard problems in hierarchical-tree clustering", Acta
Informatica 23 (1986), 311-323, doi:10.1007/BF00289116;
M. Křivánek, "The complexity of ultrametric partitions on graphs", Information Processing
Letters 27 (1988), 265-270, doi:10.1016/0020-0190(88)90090-7, problem (P6).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HierarchicalTreeClusteringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HierarchicalTreeClustering

open Cslib.Bioinformatics.Phylogenetics.Splits (IsUltrametric)

/-!
# HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting) is NP-complete

INSTANCE: a finite set `X = {x₁, …, xₙ}` with a dissimilarity `w` on `X` (symmetric, and
`w(x, y) = 0` exactly when `x = y`), and a positive integer `K`.
QUESTION: is there an ultrametric `u` on `X` with
`σ(u, w) = ∑_{x < y} |u(x, y) - w(x, y)| ≤ K`?

This is problem (P6) of Křivánek (1988), who records that its NP-completeness was proved by
Křivánek and Morávek (1986). An ultrametric is a metric `u` with
`u(x, z) ≤ max {u(x, y), u(y, z)}`; it is CSLib's
`Cslib.Bioinformatics.Phylogenetics.Splits.IsUltrametric` (symmetric, zero on the diagonal,
positive off the diagonal, three-point condition), with real values.

The objects are `Fin n` and `w` is given by the rows of an `n × n` matrix of natural numbers in
binary encoding. Křivánek states the problem for positive rational dissimilarities; an instance
with rational `w` and integer `K` is equivalent to the integer instance obtained by multiplying
`w` and `K` by a common denominator. Since `w` is integral, some optimal `u` takes its values
in the range of `w` (ℓ₁ isotonic regression over the clusters of `u`), so real, rational and
integer ultrametrics give the same answer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting) is NP-complete.** Source: Křivánek
and Morávek (1986); Křivánek (1988), problem (P6). -/
public theorem_wanted hierarchicalTreeClustering_npComplete :
    hierarchicalTreeClusteringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hierarchicalTreeClusteringDec

end MetaMathlibExt.Complexity.NPComplete.HierarchicalTreeClustering
