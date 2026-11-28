/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MASTERMIND SATISFIABILITY is NP-complete

Source:
J. Stuckman and G.-Q. Zhang, "Mastermind is NP-complete", INFOCOMP Journal of Computer
Science 5(2) (2006), 25-28, arXiv:cs/0512049 (Definition 2.1, Section 2.1, Theorem 2.1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MastermindSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiability

/-!
# MASTERMIND SATISFIABILITY is NP-complete

Stuckman and Zhang's Mastermind Satisfiability Problem (MSP). Codes are tuples of length `ℓ`
over `κ` colors. The Mastermind score of a guess `x` against a code `y` is the pair
`ρ(x, y) = (b, w - b)`, where `b = #{i | xᵢ = yᵢ}` counts the black pegs (right color in the
right position) and `w = ∑ⱼ min(#{i | xᵢ = j}, #{i | yᵢ = j})` counts the color matches
irrespective of position, so `w - b` counts the white pegs.

INSTANCE: a set `G` of guesses in `[κ]^ℓ`, with a Mastermind score `(b_g, w_g)` for each
`g ∈ G`. QUESTION: is there a code `s ∈ [κ]^ℓ` with `ρ(g, s) = (b_g, w_g)` for every `g ∈ G`?
The source states the problem "for `κ > 1`".

Colors are `0, …, κ - 1` instead of the source's `1, …, κ`. A guess is a list of `ℓ` colors;
the code is a function `Fin ℓ → Fin κ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MASTERMIND SATISFIABILITY is NP-complete.** Source: Stuckman and Zhang (2006),
Theorem 2.1 (membership: a code is checked against every guess; hardness: a reduction from
VERTEX COVER). -/
public theorem_wanted mastermindSatisfiability_npComplete :
    mastermindSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mastermindSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiability
