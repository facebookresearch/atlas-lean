/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SOLITAIRE UNO is NP-complete

Source:
E. D. Demaine, M. L. Demaine, N. J. A. Harvey, R. Uehara, T. Uno and Y. Uno, "UNO is hard, even
for a single player", Theoretical Computer Science 521 (2014), 51-61,
doi:10.1016/j.tcs.2013.11.023, Theorem 3 (Uno-1); arXiv:1003.2851.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SolitaireUnoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SolitaireUno

/-!
# SOLITAIRE UNO is NP-complete

Demaine, Demaine, Harvey, Uehara, Uno and Uno (2014), Section 2.2: "we define a card to be a
tuple `(x, y) ∈ X × Y`, where `X = {1, 2, …, c}` is a set of colors and `Y = {1, 2, …, b}` is a
set of numbers"; the cards form a multiset `C` ("there may be more than one card with the same
color and the same number"). "A playing (or discarding) sequence (of cards) of a card set `C` is
a sequence of cards `(t_{s_1}, …, t_{s_k})` such that `t_{s_i} ∈ C` and
`t_{s_j} ∈ C \ {t_{s_i} | i < j}` for each `j`. A playing sequence is feasible if `t_{s_{j+1}}`
matches `t_{s_j}`", and with one player a card `(x', y')` matches `(x, y)` when `x' = x` or
`y' = y`; the first card may be any card (assumption (e)). Uno-1 (Cooperative Uno with one
player) asks whether the player can make the card set empty, i.e. play every card. Theorem 3:
Uno-1 is NP-complete.

INSTANCE: numbers `c` and `b`, and a multiset `C` of cards `(x, y)` with `1 ≤ x ≤ c`,
`1 ≤ y ≤ b`.
QUESTION: is there a feasible playing sequence of all the cards of `C`?

Representation. The multiset `C` is a list of cards; a playing sequence of all of `C` is a
rearrangement of that list (`List.Perm`), and feasibility says that consecutive cards share
their color or their number (`List.IsChain`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SOLITAIRE UNO is NP-complete.** Source: Demaine, Demaine, Harvey, Uehara, Uno and Uno
(2014), Theorem 3. -/
public theorem_wanted solitaireUno_npComplete :
    solitaireUnoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L solitaireUnoDec

end MetaMathlibExt.Complexity.NPComplete.SolitaireUno
