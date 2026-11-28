/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COPELAND^α CONSTRUCTIVE CONTROL BY ADDING VOTERS: definitions

Source:
P. Faliszewski, E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Llull and Copeland voting
computationally resist bribery and constructive control", Journal of Artificial Intelligence
Research 35 (2009), 275-341, doi:10.1613/jair.2697 (Definition 2.1; problem E-CCAV, Section 2.3;
Theorem 4.17: for each rational `α` with `0 ≤ α ≤ 1`, Copeland^α is resistant to constructive
control via adding voters in the unique-winner model).
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle
public import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVoters

open CondorcetConstructiveControlByAddingVoters
  (CondorcetConstructiveControlByAddingVotersInstance profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers)

open Classical in
/-- The Copeland^α score of candidate `a` under profile `P`: one point for each other candidate
`b` that a majority prefers `a` to, plus `α` points for each other candidate `b` tied with `a`
(no majority either way). -/
noncomputable def copelandScore (α : ℚ) {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : MathlibExt.GameTheory.SocialChoice.ArrowWanted.Profile Alt Voter) (a : Alt) : ℚ :=
  ((Finset.univ.filter fun b => b ≠ a ∧ MajorityPrefers P a b).card : ℚ) +
    α * ((Finset.univ.filter fun b =>
      b ≠ a ∧ ¬ MajorityPrefers P a b ∧ ¬ MajorityPrefers P b a).card : ℚ)

/-- Candidate `p` is the unique Copeland^α winner of the election `E` (a list of votes over
`m` candidates): every other candidate has a smaller Copeland^α score. -/
def IsUniqueCopelandWinner (α : ℚ) (m : ℕ) (E : List (List ℕ)) (p : ℕ) : Prop :=
  ∀ a d : Fin m, (a : ℕ) = p → d ≠ a →
    copelandScore α (profile m E) d < copelandScore α (profile m E) a

/-- Well-formedness of an instance: every registered and unregistered vote is a strict ranking
of all `m` candidates, and `p` is a candidate. -/
def WellFormed (i : CondorcetConstructiveControlByAddingVotersInstance) : Prop :=
  (∀ v ∈ i.2.1, v.Perm (List.range i.1)) ∧ (∀ v ∈ i.2.2.1, v.Perm (List.range i.1)) ∧
    i.2.2.2.1 < i.1

/-- At most `k` voters `Q ⊆ W` whose registration makes `p` the unique Copeland^α winner of
`V ++ Q`. -/
def CopelandConstructiveControlByAddingVotersFeasible (α : ℚ)
    (i : CondorcetConstructiveControlByAddingVotersInstance) : Prop :=
  ∃ Q : List (List ℕ), Q.Sublist i.2.2.1 ∧ Q.length ≤ i.2.2.2.2 ∧
    IsUniqueCopelandWinner α i.1 (i.2.1 ++ Q) i.2.2.2.1

open Classical in
/-- COPELAND^α CONSTRUCTIVE CONTROL BY ADDING VOTERS as a decision problem over bitstrings. -/
noncomputable def copelandConstructiveControlByAddingVotersDec (α : ℚ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CondorcetConstructiveControlByAddingVotersInstance) x with
  | some i => decide (WellFormed i ∧ CopelandConstructiveControlByAddingVotersFeasible α i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVoters
