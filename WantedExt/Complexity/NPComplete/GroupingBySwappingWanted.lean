/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GROUPING BY SWAPPING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR21] GROUPING BY SWAPPING (attributed to
T. D. Howell, "Grouping by swapping is NP-complete", unpublished manuscript (1977)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GroupingBySwappingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GroupingBySwapping

/-!
# GROUPING BY SWAPPING is NP-complete

INSTANCE: a finite alphabet `Σ`, a string `x ∈ Σ*`, and a positive integer `K`. QUESTION: is
there a sequence of `K` or fewer adjacent symbol interchanges that converts `x` into a string
`y` in which all occurrences of each symbol `a ∈ Σ` are in a single block, i.e. `y` has no
subsequences of the form `a b a` for `a, b ∈ Σ` and `a ≠ b`?

This is Garey and Johnson's [SR21] (p. 231), with reference [Howell, 1977] (an unpublished
manuscript, "Grouping by swapping is NP-complete", per their bibliography), transformation from
FEEDBACK EDGE SET; the original was not available. Membership in NP: a shortest sequence of
interchanges from `x` to a given rearrangement `y` has at most `|x| (|x| - 1) / 2` steps (the
number of inversions), so a shortest witnessing sequence is a polynomial certificate even when
`K` is large.

The alphabet is `Σ = {0, ..., s - 1}` and strings are lists of symbols. One interchange is
`Swap a b`: `b` is `a` with two adjacent symbols interchanged (the interchange operation of
`StringToStringCorrection.Step`). As in `StringToStringCorrection`, a sequence of at most `K`
interchanges is a list of strings `x = w₀, w₁, ..., w_j = y` with `j ≤ K` (so at most `K + 1`
strings) in which each consecutive pair is one `Swap` (`List.IsChain`); `j = 0` (no
interchange, `y = x`) is included. A subsequence is a `List.Sublist`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GROUPING BY SWAPPING is NP-complete.** Source: Garey and Johnson (1979), [SR21]; Howell
(1977, unpublished). -/
public theorem_wanted groupingBySwapping_npComplete :
    groupingBySwappingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L groupingBySwappingDec

end MetaMathlibExt.Complexity.NPComplete.GroupingBySwapping
