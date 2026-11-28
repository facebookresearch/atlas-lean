/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet) is NP-complete

Source:
I. Elias, "Settling the intractability of multiple alignment", Journal of Computational
Biology 13 (2006), 1323-1339, doi:10.1089/cmb.2006.13.1323 (NP-hard for every metric over a
binary or larger alphabet, in particular the unit metric);
earlier: L. Wang and T. Jiang, "On the complexity of multiple sequence alignment", Journal of
Computational Biology 1 (1994), 337-348, doi:10.1089/cmb.1994.1.337 (a non-metric score).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipleSequenceAlignmentSPScoreDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleSequenceAlignmentSPScore

/-!
# MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet) is NP-complete

INSTANCE: strings `s₁, …, s_k` over the binary alphabet `{0, 1}` (`k` is part of the input) and
a non-negative integer `K`. QUESTION: is there a multiple alignment of `s₁, …, s_k` whose
sum-of-pairs (SP) score under the unit metric is at most `K`? A multiple alignment pads every
`sᵢ` with gaps `-` to a common length, with no column consisting of gaps only; its SP-score is
the sum over all pairs `i < j` of rows and over all columns of `d(x, y)`, where `x` and `y` are
the symbols of rows `i` and `j` in the column and the unit metric `d` on `{0, 1, -}` is `0` on
equal symbols and `1` on distinct ones.

The alignment and its SP-score are CSLib's: an alignment is
`Cslib.Algorithms.Lean.MSAlignment k Bool`, a list of columns, each assigning every row a letter
(`some b`) or a gap (`none`); `Cslib.Algorithms.Lean.IsMSAlignment` says no column is all gaps
and row `i` with its gaps removed is `sᵢ`; `Cslib.Algorithms.Lean.msaScore σ gap` is the SP-score
with substitution score `σ`, score `gap` for a letter against a gap and `0` for two gaps. The unit
metric is `σ a b = if a = b then 0 else 1` with `gap = 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPLE SEQUENCE ALIGNMENT WITH SP-SCORE (unit metric, binary alphabet) is
NP-complete.** Source: Elias (2006). -/
public theorem_wanted multipleSequenceAlignmentSPScore_npComplete :
    multipleSequenceAlignmentSPScoreDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleSequenceAlignmentSPScoreDec

end MetaMathlibExt.Complexity.NPComplete.MultipleSequenceAlignmentSPScore
