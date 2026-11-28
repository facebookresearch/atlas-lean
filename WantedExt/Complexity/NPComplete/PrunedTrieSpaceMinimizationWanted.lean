/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRUNED TRIE SPACE MINIMIZATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR3] PRUNED TRIE SPACE MINIMIZATION, p. 226
(reference [Comer and Sethi, 1976]; transformation from 3DM);
D. Comer and R. Sethi, "The complexity of trie index construction", Journal of the ACM 24
(1977), 428-440, doi:10.1145/322017.322023 (Theorem 3(a)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrunedTrieSpaceMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrunedTrieSpaceMinimization

/-!
# PRUNED TRIE SPACE MINIMIZATION is NP-complete

INSTANCE: a finite set `S`, a collection `F` of functions `f : S → ℤ⁺`, and a positive integer
`K`.
QUESTION: is there a sequence `⟨f₁, f₂, …, f_m⟩` of distinct functions from `F` such that for
every two elements `a, b ∈ S` there is some `i`, `1 ≤ i ≤ m`, for which `fᵢ(a) ≠ fᵢ(b)`, and
such that, if `N(i)` denotes the number of distinct `i`-tuples `X = (x₁, x₂, …, xᵢ)` for which
there is more than one `a ∈ S` having `(f₁(a), f₂(a), …, fᵢ(a)) = X`, then
`∑_{i=1}^{m} N(i) ≤ K`?

`N(i)` is the number of nonleaf nodes at depth `i` of the pruned trie that tests `f₁, …, f_m`
in this order (Comer and Sethi); "every two elements" means every two distinct elements.

The elements of `S` are `0, …, s - 1`, the elements of `Fin s`. A function `f : S → ℤ⁺` is the
list `[f(0), …, f(s - 1)]` of its values; `F` is a duplicate-free list of such lists, and a
sequence of distinct functions from `F` is a duplicate-free list of members of `F`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRUNED TRIE SPACE MINIMIZATION is NP-complete.** Source: Garey and Johnson (1979), [SR3];
Comer and Sethi (1977). -/
public theorem_wanted prunedTrieSpaceMinimization_npComplete :
    prunedTrieSpaceMinimizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L prunedTrieSpaceMinimizationDec

end MetaMathlibExt.Complexity.NPComplete.PrunedTrieSpaceMinimization
