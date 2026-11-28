/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for Borda with three candidates is NP-complete

Source:
V. Conitzer, T. Sandholm and J. Lang, "When are elections with few candidates hard to
manipulate?", Journal of the ACM 54(3) (2007), Article 14, doi:10.1145/1236457.1236461,
Definition 1, Theorem 6 and Corollary 1 (reduction from PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CoalitionalManipulationBordaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda

/-!
# CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for Borda with three candidates is NP-complete

INSTANCE: three candidates, a set `S` of weighted votes (the nonmanipulators' votes), the
weights of a set `T` of votes that are still open (the manipulators' votes), and a preferred
candidate `p`.
QUESTION: is there a way to cast the votes in `T` so that `p` wins the election under the Borda
protocol?

A vote ranks the candidates; a voter of weight `w` counts as `w` voters. Under the positional
scoring protocol with vector `α = (α₁, α₂, α₃)`, a candidate receives `α₁` points from each
voter ranking it first, `α₂` from each ranking it second, and `α₃` from each ranking it third,
and the candidate with the highest score wins. The Borda protocol for three candidates is the
scoring protocol with `α = (2, 1, 0)`. As in the source, a manipulation that leaves `p` tied for
the win is not successful: `p` must score strictly more than each other candidate.

The candidates are `0, 1, 2`, and a vote is a list of them in order of preference (a
permutation of `[0, 1, 2]`, most preferred first). Weights are natural numbers, as in the
source (a weight function `V → ℕ`), in the canonical binary encoding; the source's hardness
proof reduces from PARTITION, so the weights carry the hardness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSTRUCTIVE COALITIONAL WEIGHTED MANIPULATION for Borda with three candidates is
NP-complete.** Source: Conitzer, Sandholm and Lang (2007), Corollary 1. -/
public theorem_wanted coalitionalManipulationBorda_npComplete :
    coalitionalManipulationBordaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coalitionalManipulationBordaDec

end MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda
