/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COPELAND^α MANIPULATION with two manipulators is NP-complete

Source:
P. Faliszewski, E. Hemaspaandra and H. Schnoor, "Copeland voting: ties matter", Proceedings of
the 7th International Joint Conference on Autonomous Agents and Multiagent Systems (AAMAS 2008),
983-990 (Definition 2.1; the problem E-manipulation, Section 2; Theorem 3.1, proved by Lemmas
3.2 and 3.3 with two manipulative voters).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BordaManipulationTwoManipulatorsWanted
public import WantedExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersWanted
public import WantedExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVotersWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CopelandManipulationTwoManipulators

open BordaManipulationTwoManipulators (BordaManipulationInstance IsVote WellFormed)
open CondorcetConstructiveControlByAddingVoters (profile)
open CopelandConstructiveControlByAddingVoters (copelandScore)

/-!
# COPELAND^α MANIPULATION with two manipulators is NP-complete

Fix a rational `α` with `0 < α < 1` and `α ≠ 1/2`.
INSTANCE: an election with a set `C` of candidates and a multiset `V` of (nonmanipulative)
voters with fixed preference lists over `C`, and a distinguished candidate `p ∈ C`.
QUESTION: can the preference lists of two manipulative voters `W = {w₁, w₂}` be set so that `p`
is a Copeland^α winner of the election with voters `V ∪ W`?

Copeland^α (Faliszewski, Hemaspaandra and Schnoor, Definition 2.1): a candidate wins its
head-to-head contest with another candidate if more voters prefer it to the other than the
other way round, and the two tie if equally many voters prefer each; the Copeland^α score of a
candidate is the number of candidates it defeats plus `α` times the number of candidates it ties
with, and the candidates with the highest score are the winners. Voters are unweighted and
their preferences are strict linear orders. Theorem 3.1 states that Copeland^α-manipulation is
NP-complete for each such `α`; the reductions of Lemmas 3.2 (`0 < α < 1/2`) and 3.3
(`1/2 < α < 1`) use exactly two manipulative voters, so the problem with two manipulators is
NP-complete (membership in NP: the two manipulative votes are a certificate).

Representation, shared with `BordaManipulationTwoManipulatorsWanted` (instance, votes,
well-formedness): the candidates are `0, …, m - 1`, a vote is a list of all of them, best first,
and `V` is a list of votes (two voters may cast the same vote). The score is
`CopelandConstructiveControlByAddingVoters.copelandScore`, evaluated on the profile
`CondorcetConstructiveControlByAddingVoters.profile` of the election `V ++ [w₁, w₂]`; its
"majority" is the repository's `CondorcetCycle.MajorityPrefers` (strictly more than half of the
voters), which with strict preferences is the same as more voters preferring `a` to `b` than
`b` to `a`. The parameter `α` is fixed, as in the source, so there is one decision problem for
each `α`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **COPELAND^α MANIPULATION with two manipulators is NP-complete for every rational `α` with
`0 < α < 1` and `α ≠ 1/2`.** Source: Faliszewski, Hemaspaandra and Schnoor (2008), Theorem 3.1
(Lemmas 3.2 and 3.3). -/
public theorem_wanted copelandManipulation_npComplete (α : ℚ) (h₀ : 0 < α) (h₁ : α < 1)
    (hα : α ≠ 1 / 2) :
    copelandManipulationDec α ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (copelandManipulationDec α)

end MetaMathlibExt.Complexity.NPComplete.CopelandManipulationTwoManipulators
