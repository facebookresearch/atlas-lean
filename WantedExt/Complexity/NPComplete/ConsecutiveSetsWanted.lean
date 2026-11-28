/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSECUTIVE SETS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR18] CONSECUTIVE SETS;
L. T. Kou, "Polynomial complete consecutive information retrieval problems", SIAM Journal on
Computing 6 (1977), 67-75, doi:10.1137/0206004.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConsecutiveSetsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsecutiveSets

/-!
# CONSECUTIVE SETS is NP-complete

INSTANCE: a finite alphabet `Σ`, a collection `C = {Σ₁, Σ₂, ..., Σₙ}` of subsets of `Σ`, and a
positive integer `K`. QUESTION: is there a string `w ∈ Σ*` with `|w| ≤ K` such that, for each
`i`, the elements of `Σᵢ` occur in a consecutive block of `|Σᵢ|` symbols of `w`?

The alphabet is `Σ = {0, ..., s - 1}`. Each subset `Σᵢ` is a list of symbols without
repetitions, so `|Σᵢ|` is its length. The elements of `Σᵢ` occur in a consecutive block of
`|Σᵢ|` symbols of `w` exactly when some contiguous sublist (`List.IsInfix`) of `w` is a
permutation (`List.Perm`) of `Σᵢ`: a block of `|Σᵢ|` symbols containing the `|Σᵢ|` elements of
`Σᵢ` contains each exactly once. Symbols may repeat in `w`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSECUTIVE SETS is NP-complete.** Source: Garey and Johnson (1979), [SR18]; Kou
(1977). -/
public theorem_wanted consecutiveSets_npComplete :
    consecutiveSetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consecutiveSetsDec

end MetaMathlibExt.Complexity.NPComplete.ConsecutiveSets
