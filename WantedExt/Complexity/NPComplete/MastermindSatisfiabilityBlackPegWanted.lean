/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MASTERMIND SATISFIABILITY with black-peg results is NP-complete

Source:
M. T. Goodrich, "On the algorithmic complexity of the Mastermind game with black-peg
results", Information Processing Letters 109(13) (2009), 675-678,
doi:10.1016/j.ipl.2009.02.021, arXiv:0904.4911 (Section 2, Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MastermindSatisfiabilityBlackPegDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiabilityBlackPeg

open MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiability (blackPegs)

/-!
# MASTERMIND SATISFIABILITY with black-peg results is NP-complete

Goodrich's single-count (black-peg) Mastermind satisfiability. Codes are vectors of length
`N` over an alphabet of `K` colors, and a guess `Vᵢ` is scored only by its black count
`b(Vᵢ) = |{j : Vᵢ[j] = V[j]}|`, the number of positions where it matches the hidden vector
`V` (`MastermindSatisfiability.blackPegs`, the black half of the double-count score).

INSTANCE: a sequence of guesses `V₁, …, V_m` of length `N` over `K` colors, with responses
`b(V₁), …, b(V_m)`. QUESTION: is there a vector `V` that satisfies all of these responses?

Colors are `0, …, K - 1`. A guess is a list of `N` colors; the hidden vector is a function
`Fin N → Fin K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MASTERMIND SATISFIABILITY with black-peg results is NP-complete.** Source: Goodrich
(2009), Theorem 1 (membership: guess `V` and check every response; hardness: a reduction from
3-DIMENSIONAL MATCHING). -/
public theorem_wanted mastermindSatisfiabilityBlackPeg_npComplete :
    mastermindSatisfiabilityBlackPegDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mastermindSatisfiabilityBlackPegDec

end MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiabilityBlackPeg
