/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRUNED TRIE ACCESS TIME MINIMIZATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR3] PRUNED TRIE SPACE MINIMIZATION, p. 226,
comment: the related "access time minimization" problem is also NP-complete for pruned tries
(the entry's reference is [Comer and Sethi, 1976]);
D. Comer and R. Sethi, "The complexity of trie index construction", Journal of the ACM 24
(1977), 428-440, doi:10.1145/322017.322023 (Problem 3, least access time pruned trie;
Theorem 1 and Appendix C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrunedTrieAccessTimeMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrunedTrieAccessTimeMinimization

open PrunedTrieSpaceMinimization

/-!
# PRUNED TRIE ACCESS TIME MINIMIZATION is NP-complete

INSTANCE: a finite set `S`, a collection `F` of functions `f : S → ℤ⁺`, and a positive integer
`K`, as in PRUNED TRIE SPACE MINIMIZATION.
QUESTION: is there a sequence `⟨f₁, f₂, …, f_m⟩` of functions from `F` that distinguishes every
two elements of `S` (for every two elements `a, b ∈ S` there is some `i`, `1 ≤ i ≤ m`, with
`fᵢ(a) ≠ fᵢ(b)`) and for which `∑_{a ∈ S} L(a) ≤ K`, where `L(a)` is the least `i` for which no
other `b ∈ S` has `(f₁(b), f₂(b), …, fᵢ(b))` identical to `(f₁(a), f₂(a), …, fᵢ(a))`?

`L(a)` is the depth of the leaf of `a` in the pruned trie that tests `f₁, …, f_m` in this
order, and `∑_{a ∈ S} L(a)` is the access time of that trie (Comer and Sethi, Problem 3). For
`i ≤ m` the `i`-tuple of `a` is `prefixTuple fs i a`; since the sequence distinguishes every two
elements, `i = m` has the property, so `L(a) ≤ m`. The empty tuple (`i = 0`) has the property
only when `S = {a}`, where the leaf is the root, at depth `0`; then `∑ L(a) = 0`, and since `K`
is positive this boundary case is a yes-instance under either indexing convention.

The instance encoding, `WellFormed`, `value`, `prefixTuple`, and `Distinguishes` are those of
`PrunedTrieSpaceMinimization`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRUNED TRIE ACCESS TIME MINIMIZATION is NP-complete.** Source: Garey and Johnson (1979),
[SR3] (comment); Comer and Sethi (1977). -/
public theorem_wanted prunedTrieAccessTimeMinimization_npComplete :
    prunedTrieAccessTimeMinimizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L prunedTrieAccessTimeMinimizationDec

end MetaMathlibExt.Complexity.NPComplete.PrunedTrieAccessTimeMinimization
