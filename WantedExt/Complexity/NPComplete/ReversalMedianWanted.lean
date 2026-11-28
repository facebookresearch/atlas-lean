/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REVERSAL MEDIAN is NP-complete

Source:
A. Caprara, "The reversal median problem", INFORMS Journal on Computing 15 (2003), 93-113,
doi:10.1287/ijoc.15.1.93.15155;
the hardness for three genomes is recorded by M. Bader, "The transposition median problem is
NP-complete", Theoretical Computer Science 412 (2011), 1099-1110,
doi:10.1016/j.tcs.2010.12.009.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ReversalMedianDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReversalMedian

/-!
# REVERSAL MEDIAN is NP-complete

A genome with `n` genes is a signed permutation: a sequence `(π₁, …, π_n)` of the genes
`1, …, n`, each exactly once, each with an orientation `+` or `-`. The reversal `ρ(a, b)`,
`1 ≤ a ≤ b ≤ n`, reverses the order of the segment `π_a, …, π_b` and flips the orientation of
each of its genes. The reversal distance `d(σ, π)` is the minimum number of reversals that
transform `σ` into `π`. INSTANCE: three signed permutations `π¹, π², π³` of `n` genes and a
non-negative integer `K`. QUESTION: is there a signed permutation `σ` of the `n` genes with
`d(σ, π¹) + d(σ, π²) + d(σ, π³) ≤ K`?

Genes are `0, …, n - 1` and positions `0, …, n - 1`; a signed permutation is a list of pairs
(gene, orientation), the orientation `true` meaning `-`. A reversal is a pair `(a, b)` of
positions with `a ≤ b < n`. The sum of the three distances is at most `K` exactly when there are
three sequences of reversals, transforming `σ` into `π¹`, `π²` and `π³`, of total length at most
`K`, which is how the question is stated.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REVERSAL MEDIAN is NP-complete.** Source: Caprara (2003). -/
public theorem_wanted reversalMedian_npComplete :
    reversalMedianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L reversalMedianDec

end MetaMathlibExt.Complexity.NPComplete.ReversalMedian
