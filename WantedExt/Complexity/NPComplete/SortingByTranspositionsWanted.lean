/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SORTING BY TRANSPOSITIONS is NP-complete

Source:
L. Bulteau, G. Fertin and I. Rusu, "Sorting by transpositions is difficult", SIAM Journal on
Discrete Mathematics 26 (2012), 1148-1180, doi:10.1137/110851390, arXiv:1011.1157.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SortingByTranspositionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions

/-!
# SORTING BY TRANSPOSITIONS is NP-complete

Bulteau, Fertin and Rusu (2012), Section 1: `n` is a positive integer and permutations are
permutations of `⟦0 ; n⟧` with `0` and `n` fixed points. A transposition exchanges two
consecutive factors of a sequence: for `0 < i < j < k ≤ n`, composing `π` with the
transposition `τ_{i,j,k}` (Definition 1) exchanges the factor of `π` in positions
`i, …, j - 1` with the factor in positions `j, …, k - 1`. The transposition distance `d_t(π)`
is the least `k` with `π ∘ τ_k ∘ ⋯ ∘ τ_1 = Id_n` (Definition 3). SORTING BY TRANSPOSITIONS:
given a permutation `π` and an integer `k`, is `d_t(π) ≤ k`? The paper proves it NP-hard; it
is in NP.

The permutation is the list `[π(0), π(1), …, π(n)]`, a permutation of `List.range (n + 1)`
with first entry `0` and last entry `n`; `transposition` exchanges the two factors.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SORTING BY TRANSPOSITIONS is NP-complete.** Source: Bulteau, Fertin and Rusu (2012). -/
public theorem_wanted sortingByTranspositions_npComplete :
    sortingByTranspositionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sortingByTranspositionsDec

end MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions
