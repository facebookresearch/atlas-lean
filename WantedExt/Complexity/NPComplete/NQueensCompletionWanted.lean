/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# N-QUEENS COMPLETION is NP-complete

Source:
I. P. Gent, C. Jefferson and P. Nightingale, "Complexity of n-Queens Completion",
Journal of Artificial Intelligence Research 59 (2017), 815-848, doi:10.1613/jair.5512
(Problem 2; Theorem 37).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.NQueensCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NQueensCompletion

/-!
# N-QUEENS COMPLETION is NP-complete

Following Gent, Jefferson and Nightingale (2017), a queen is a pair `(α, β)` of natural
numbers: `α` is its column and `β` its row. Two queens attack each other when they are not
equal and share a column, a row, a sum-diagonal `α + β`, or a difference-diagonal `α - β`
(an integer). A solution to `n`-Queens (for `n ≥ 1`) is a set of `n` queens that all fit on
board size `n` (both coordinates below `n`) and no two of which attack each other.

INSTANCE: an integer `n ≥ 1` and a set `P` of queens that all fit on board size `n`, no two of
which have the same column or the same row.
QUESTION: is there a solution `S` to `n`-Queens with `P ⊆ S`?

As in the source, the queens of `P` need not be mutually non-attacking along diagonals (if two
of them attack on a diagonal, the answer is no).

The instance is the `n × n` board, row by row: entry `α` of row `β` is `true` when the queen
`(α, β)` is in `P`. The source assumes that the encoding of an instance has size bounded below
by `n` and polynomial in `n`; the explicit board (`n²` cells) meets this, while a binary `n`
with a list of `P` would not (a solution lists `n` queens).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **N-QUEENS COMPLETION is NP-complete.** Source: Gent, Jefferson and Nightingale (2017),
Theorem 37. -/
public theorem_wanted nQueensCompletion_npComplete :
    nQueensCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nQueensCompletionDec

end MetaMathlibExt.Complexity.NPComplete.NQueensCompletion
