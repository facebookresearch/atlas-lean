/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STABLE MODEL EXISTENCE: definitions

Source:
W. Marek and M. Truszczyński, "Autoepistemic logic", Journal of the ACM 38 (1991), 588-619,
doi:10.1145/116825.116836 ("it is proven that the problem of existence of stable models is
NP-complete"); stable models: M. Gelfond and V. Lifschitz, "The stable model semantics for logic
programming", Logic Programming: Proceedings of the Fifth International Conference and Symposium
(ICLP/SLP 1988), MIT Press, 1070-1080.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Algorithms.SAT.Horn.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StableModelExistence

open Cslib.Logic.LegacyPL (CNF)

/-- An instance: the rules of the program, `(a, [b₁, …, bₖ], [c₁, …, cₗ])` standing for
`a ← b₁, …, bₖ, not c₁, …, not cₗ`. -/
abbrev StableModelExistenceInstance := List (ℕ × List ℕ × List ℕ)

/-- The Gelfond-Lifschitz reduct `P^M` as a Horn formula: every rule none of whose negated atoms
lies in `M` contributes the clause `a ∨ ¬b₁ ∨ … ∨ ¬bₖ` of its definite part `a ← b₁, …, bₖ`; the
other rules are deleted. -/
def reduct (P : StableModelExistenceInstance) (M : Finset ℕ) : CNF :=
  (P.filter fun r => r.2.2.all fun c => c ∉ M).map fun r =>
    (r.1, true) :: r.2.1.map fun b => (b, false)

/-- `M` is a stable model of `P`: it is the least model of the reduct `P^M`. -/
def IsStableModel (P : StableModelExistenceInstance) (M : Finset ℕ) : Prop :=
  Cslib.Algorithms.SAT.Horn.close (reduct P M) ∅ = M

/-- The program has a stable model. -/
def StableModelExistenceFeasible (P : StableModelExistenceInstance) : Prop :=
  ∃ M : Finset ℕ, IsStableModel P M

open Classical in
/-- STABLE MODEL EXISTENCE as a decision problem over bitstrings. -/
noncomputable def stableModelExistenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StableModelExistenceInstance) x with
  | some P => decide (StableModelExistenceFeasible P)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StableModelExistence
