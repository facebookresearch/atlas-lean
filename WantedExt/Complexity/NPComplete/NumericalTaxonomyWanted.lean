/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NUMERICAL TAXONOMY is NP-complete

Source:
R. Agarwala, V. Bafna, M. Farach, M. Paterson and M. Thorup, "On the approximability of
numerical taxonomy (fitting distances by tree metrics)", SIAM Journal on Computing 28 (1999),
1073-1085, doi:10.1137/S0097539795296334, Section 5, Theorem 5.1 (also University of Warwick
Department of Computer Science Research Report CS-RR-330, 1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NumericalTaxonomyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NumericalTaxonomy

open MathlibExt.Biology.Phylogenetics.Buneman (IsTreeMetric)

/-!
# NUMERICAL TAXONOMY is NP-complete

INSTANCE: a distance matrix `D : S² → ℝ≥0` on a set `S = {1, …, n}` of points, and a threshold
`Δ ≥ 0`. QUESTION: is there a tree metric `T` which spans `S` and for which `‖T - D‖∞ ≤ Δ`?

This is the decision version of the numerical taxonomy problem under the `L∞` norm (Agarwala et
al., Section 5, Theorem 5.1). A tree metric is defined by a weighted tree spanning the points:
the distance between two points is the sum of the weights of the edges of the path between them
(Section 1); this is `IsTreeMetric` of `MathlibExt.Combinatorics.SimpleGraph.TreeMetric` (positive edge
lengths, Steiner vertices allowed). A tree metric is a metric (Definition 2.1, Theorem 2.3), so
distinct points are at positive distance, which `IsTreeMetric` alone does not require (it lets
taxa share a vertex); `NumericalTaxonomyFeasible` adds it. The norm is
`‖M‖∞ = max_{i<j} |M[i, j]|` (Definition 2.6).

The entries of `D` and the threshold `Δ` are nonnegative rationals, each given as a pair
`(numerator, denominator)` of natural numbers with a positive denominator; numbers use the binary
encoding. Points are indices `0, …, n - 1` of the rows of `D`. As a distance matrix, `D` is
square, symmetric and zero on the diagonal (`WellFormed`, compared as rationals).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NUMERICAL TAXONOMY is NP-complete.** Source: Agarwala, Bafna, Farach, Paterson and Thorup
(1999), Theorem 5.1. -/
public theorem_wanted numericalTaxonomy_npComplete :
    numericalTaxonomyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L numericalTaxonomyDec

end MetaMathlibExt.Complexity.NPComplete.NumericalTaxonomy
