/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MASTERMIND SATISFIABILITY with black-peg results: definitions

Source:
M. T. Goodrich, "On the algorithmic complexity of the Mastermind game with black-peg
results", Information Processing Letters 109(13) (2009), 675-678,
doi:10.1016/j.ipl.2009.02.021, arXiv:0904.4911 (Section 2, Theorem 1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MastermindSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiabilityBlackPeg

open MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiability (blackPegs)

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

end MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiabilityBlackPeg
