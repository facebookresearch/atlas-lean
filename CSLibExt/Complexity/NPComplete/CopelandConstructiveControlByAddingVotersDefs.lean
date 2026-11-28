/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle
public import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersDefs

/-!
# COPELAND^α CONSTRUCTIVE CONTROL BY ADDING VOTERS: definitions

Fix a rational `α` with `0 ≤ α ≤ 1`.
INSTANCE: a set `C` of candidates, two disjoint collections of voters `V` (registered) and `W`
(unregistered), represented via preference lists over `C`, a distinguished candidate `p`, and a
nonnegative integer `k`.
QUESTION: is there a subset `Q` of the voters in `W` with `‖Q‖ ≤ k` such that `p` is the unique
Copeland^α winner of the election with voters `V ∪ Q`?

Copeland^α (Faliszewski, Hemaspaandra, Hemaspaandra and Rothe, Definition 2.1): in each
head-to-head contest between two distinct candidates, a candidate preferred by a majority of the
voters obtains one point and the other none, and if neither is preferred by a majority (a tie)
both obtain `α` points; the Copeland^α score of a candidate is the sum of its points, and `p` is
the unique winner when its score exceeds that of every other candidate.

Representation, shared with `CondorcetConstructiveControlByAddingVotersWanted`: the candidates
are `C = {0, ..., m - 1}`; a vote is a list of candidates, best first, and a well-formed vote
lists every candidate exactly once (rational voters with strict linear preferences); `V` and `W`
are lists of votes (two voters may cast the same vote), and the added voters `Q` are a sublist
of `W`. The election `V ++ Q` is turned into a profile of the repository's social-choice
library by `CondorcetConstructiveControlByAddingVoters.profile`, and "preferred by a majority"
is that library's `CondorcetCycle.MajorityPrefers` (strictly more than half of the voters).
The parameter `α` is fixed, as in the source, so there is one decision problem for each `α`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
P. Faliszewski, E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Llull and Copeland voting
computationally resist bribery and constructive control", Journal of Artificial Intelligence
Research 35 (2009), 275-341, doi:10.1613/jair.2697 (Definition 2.1; problem E-CCAV, Section 2.3;
Theorem 4.17: for each rational `α` with `0 ≤ α ≤ 1`, Copeland^α is resistant to constructive
control via adding voters in the unique-winner model).
-/

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

/-- For `p < m`, every other candidate has a strictly smaller Copeland^α score than `p` in `E`.
For `p ≥ m`, there are no comparisons and the predicate holds. -/
def IsUniqueCopelandWinner (α : ℚ) (m : ℕ) (E : List (List ℕ)) (p : ℕ) : Prop :=
  ∀ a d : Fin m, (a : ℕ) = p → d ≠ a →
    copelandScore α (profile m E) d < copelandScore α (profile m E) a

/-- Well-formedness of an instance: every registered and unregistered vote is a strict ranking
of all `m` candidates, and `p` is a candidate. -/
def WellFormed (i : CondorcetConstructiveControlByAddingVotersInstance) : Prop :=
  (∀ v ∈ i.2.1, v.Perm (List.range i.1)) ∧ (∀ v ∈ i.2.2.1, v.Perm (List.range i.1)) ∧
    i.2.2.2.1 < i.1

/-- For `p < m`, adding at most `k` voters from `W` makes `p` the unique Copeland^α winner.
For `p ≥ m`, adding no voters suffices; `WellFormed` excludes this case. -/
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
