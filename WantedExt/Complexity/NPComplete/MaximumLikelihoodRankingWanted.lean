/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LIKELIHOOD RANKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MS11] MAXIMUM LIKELIHOOD RANKING, p. 281,
crediting L. Rafsky (1977, private communication) (transformation from FEEDBACK ARC SET;
NP-complete in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumLikelihoodRankingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodRanking

/-!
# MAXIMUM LIKELIHOOD RANKING is NP-complete

INSTANCE: an `n × n` matrix `A = (aᵢⱼ)` with integer entries satisfying `aᵢⱼ + aⱼᵢ = 0` for all
`i, j ∈ {1, 2, …, n}`, and a positive integer `B`.
QUESTION: is there a matrix `B' = (bᵢⱼ)` obtained from `A` by simultaneous row and column
permutations such that `∑_{1 ≤ i < j ≤ n} min {bᵢⱼ, 0} ≥ -B`?

A simultaneous row and column permutation by `π` is Mathlib's `Matrix.submatrix A π π`, with
entries `bᵢⱼ = a_{π(i) π(j)}`. Indices are `0`-based (`Fin n`).

Encoding: each entry is a pair of naturals `(positive part, negative part)` standing for their
difference, as in `ZeroOneILP`, and `A` is a list of `n` rows of length `n`. The instance is
decoded from a bitstring with the repository's canonical `MetaMathlibExt.BitstringEncoding`.
Undecodable bitstrings, and bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM LIKELIHOOD RANKING is NP-complete.** Source: Garey and Johnson (1979), [MS11];
Rafsky (1977). -/
public theorem_wanted maximumLikelihoodRanking_npComplete :
    maximumLikelihoodRankingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLikelihoodRankingDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodRanking
