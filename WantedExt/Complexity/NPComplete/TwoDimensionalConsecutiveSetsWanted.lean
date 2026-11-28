/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-DIMENSIONAL CONSECUTIVE SETS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR19] 2-DIMENSIONAL CONSECUTIVE
SETS;
W. Lipski, Jr., "One more polynomial complete consecutive retrieval problem", Information
Processing Letters 6 (1977), 91-93, doi:10.1016/0020-0190(77)90034-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSetsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSets

/-!
# 2-DIMENSIONAL CONSECUTIVE SETS is NP-complete

INSTANCE: a finite alphabet `Σ` and a collection `C = {Σ₁, Σ₂, ..., Σₙ}` of subsets of `Σ`.
QUESTION: is there a partition of `Σ` into disjoint sets `X₁, X₂, ..., X_k` such that each `Xᵢ`
has at most one element in common with each `Σⱼ` and such that, for each `Σⱼ ∈ C`, there is an
index `l(j)` such that `Σⱼ` is contained in `X_{l(j)} ∪ X_{l(j)+1} ∪ ... ∪ X_{l(j)+|Σⱼ|-1}`?

The alphabet is `Σ = {0, ..., s - 1}`. Each subset `Σⱼ` is a list of symbols without
repetitions, so `|Σⱼ|` is its length. A partition into disjoint sets `X₀, X₁, ...` is given by
the index `g(x)` of the set containing each symbol `x`, i.e. `Xᵢ = {x ∈ Σ | g(x) = i}`;
indices start at `0`, and empty sets are allowed, as in Lipski's definition ("a sequence
X₁, ..., X_k of pairwise disjoint sets with X₁ ∪ ... ∪ X_k = X"). "Each `Xᵢ` has at most one
element in common with `Σⱼ`" says that `g` is injective on `Σⱼ`, and
`Σⱼ ⊆ X_l ∪ ... ∪ X_{l+|Σⱼ|-1}` says that `l ≤ g(x) < l + |Σⱼ|` for every `x ∈ Σⱼ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **2-DIMENSIONAL CONSECUTIVE SETS is NP-complete.** Source: Garey and Johnson (1979),
[SR19]; Lipski (1977). -/
public theorem_wanted twoDimensionalConsecutiveSets_npComplete :
    twoDimensionalConsecutiveSetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoDimensionalConsecutiveSetsDec

end MetaMathlibExt.Complexity.NPComplete.TwoDimensionalConsecutiveSets
