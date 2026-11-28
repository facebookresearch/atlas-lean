/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COPELAND^α MANIPULATION with two manipulators: definitions

Source:
P. Faliszewski, E. Hemaspaandra and H. Schnoor, "Copeland voting: ties matter", Proceedings of
the 7th International Joint Conference on Autonomous Agents and Multiagent Systems (AAMAS 2008),
983-990 (Definition 2.1; the problem E-manipulation, Section 2; Theorem 3.1, proved by Lemmas
3.2 and 3.3 with two manipulative voters).
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BordaManipulationTwoManipulatorsDefs
public import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersDefs
public import CSLibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVotersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CopelandManipulationTwoManipulators

open BordaManipulationTwoManipulators (BordaManipulationInstance IsVote WellFormed)
open CondorcetConstructiveControlByAddingVoters (profile)
open CopelandConstructiveControlByAddingVoters (copelandScore)

/-- Candidate `p` is a Copeland^α winner of the election `E` (a list of votes over `m`
candidates): no candidate has a higher Copeland^α score. -/
def IsCopelandWinner (α : ℚ) (m : ℕ) (E : List (List ℕ)) (p : ℕ) : Prop :=
  ∀ a d : Fin m, (a : ℕ) = p →
    copelandScore α (profile m E) d ≤ copelandScore α (profile m E) a

/-- Two manipulative votes `w₁, w₂` over the candidates make `p` a Copeland^α winner of the
election with votes `V ++ [w₁, w₂]`. -/
def CopelandManipulationFeasible (α : ℚ) (i : BordaManipulationInstance) : Prop :=
  ∃ w₁ w₂ : List ℕ, IsVote i.1 w₁ ∧ IsVote i.1 w₂ ∧
    IsCopelandWinner α i.1 (i.2.1 ++ [w₁, w₂]) i.2.2

open Classical in
/-- COPELAND^α MANIPULATION with two manipulators as a decision problem over bitstrings. -/
noncomputable def copelandManipulationDec (α : ℚ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BordaManipulationInstance) x with
  | some i => decide (WellFormed i ∧ CopelandManipulationFeasible α i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CopelandManipulationTwoManipulators
