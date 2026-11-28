/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SORTING BY REVERSALS is NP-complete

Source:
A. Caprara, "Sorting permutations by reversals and Eulerian cycle decompositions", SIAM
Journal on Discrete Mathematics 12 (1999), 91-110, doi:10.1137/S089548019731994X;
problem as stated in P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization
problems*, entry MINIMUM SORTING BY REVERSALS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SortingByReversalsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SortingByReversals

/-!
# SORTING BY REVERSALS is NP-complete

INSTANCE: a permutation `π` of the numbers `1` to `n` and a nonnegative integer `K`.
QUESTION: is there a sequence `ρ₁, ρ₂, …, ρₜ` of reversals of intervals with `t ≤ K` such that
`π · ρ₁ · ρ₂ ⋯ ρₜ` is the identity permutation? A reversal of an interval `[i, j]` is the
permutation `(1, 2, …, i - 1, j, j - 1, …, i + 1, i, j + 1, …, n)`; composing `π` with it
reverses the block of entries of `π` in positions `i` through `j`. This is the decision form
(at most `K` reversals) of MINIMUM SORTING BY REVERSALS, which Caprara (1999) proved NP-hard.
Reversals are unsigned.

The permutation is the list `[π(1), …, π(n)]`, a permutation of `List.range' 1 n`; a reversal
`(i, j)` with `0`-based positions `i < j < n` reverses the entries in positions `i` through `j`
(`reversal`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SORTING BY REVERSALS is NP-complete.** Source: Caprara (1999); Crescenzi and Kann, MINIMUM
SORTING BY REVERSALS. -/
public theorem_wanted sortingByReversals_npComplete :
    sortingByReversalsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sortingByReversalsDec

end MetaMathlibExt.Complexity.NPComplete.SortingByReversals
