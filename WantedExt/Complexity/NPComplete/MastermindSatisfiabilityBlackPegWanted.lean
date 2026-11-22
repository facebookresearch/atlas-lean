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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MastermindSatisfiabilityWanted

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

/-- An instance `(K, N, Q)`: the number of colors `K`, the vector length `N`, and the sequence
`Q` of guesses `Vᵢ` with their black-peg responses `b(Vᵢ)`. -/
abbrev MastermindSatisfiabilityBlackPegInstance := ℕ × ℕ × List (List ℕ × ℕ)

/-- Well-formedness of an instance `(K, N, Q)`: every guess is a vector of `N` colors below
`K`. -/
def WellFormed (i : MastermindSatisfiabilityBlackPegInstance) : Prop :=
  ∀ q ∈ i.2.2, q.1.length = i.2.1 ∧ ∀ c ∈ q.1, c < i.1

/-- Some vector `V : Fin N → Fin K` has black count `b(Vᵢ)` against every guess `Vᵢ`. -/
def MastermindSatisfiabilityBlackPegFeasible
    (i : MastermindSatisfiabilityBlackPegInstance) : Prop :=
  ∃ V : Fin i.2.1 → Fin i.1, ∀ q ∈ i.2.2, blackPegs q.1 V = q.2

open Classical in
/-- MASTERMIND SATISFIABILITY with black-peg results as a decision problem over
bitstrings. -/
noncomputable def mastermindSatisfiabilityBlackPegDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MastermindSatisfiabilityBlackPegInstance) x with
  | some i => decide (WellFormed i ∧ MastermindSatisfiabilityBlackPegFeasible i)
  | none => false

/-- **MASTERMIND SATISFIABILITY with black-peg results is NP-complete.** Source: Goodrich
(2009), Theorem 1 (membership: guess `V` and check every response; hardness: a reduction from
3-DIMENSIONAL MATCHING). -/
public theorem_wanted mastermindSatisfiabilityBlackPeg_npComplete :
    mastermindSatisfiabilityBlackPegDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mastermindSatisfiabilityBlackPegDec

end MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiabilityBlackPeg
