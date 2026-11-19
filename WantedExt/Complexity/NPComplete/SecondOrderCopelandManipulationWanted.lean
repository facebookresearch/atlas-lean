/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SECOND-ORDER COPELAND MANIPULATION (unique winner) is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "The computational difficulty of manipulating
an election", Social Choice and Welfare 6 (1989), 227-241, doi:10.1007/BF00295861,
Section 4, Theorem 3 (Existence of a Winning Preference for second-order Copeland).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Sets
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SecondOrderCopelandManipulation

open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers)

/-!
# SECOND-ORDER COPELAND MANIPULATION (unique winner) is NP-complete

INSTANCE: a set `C` of candidates, a distinguished candidate `p ∈ C`, and a collection `V` of
sincere votes, each a strict, transitive and complete preference order on `C`.
QUESTION: is there a preference order `P` on `C` for one additional voter (the manipulator)
such that `p` is the unique winner of the election with votes `V` and `P` under second-order
Copeland?

Second-order Copeland (Bartholdi, Tovey and Trick 1989, Section 4): a candidate `a` wins the
pairwise contest against `b` when a majority of the voters prefers `a` to `b`; the Copeland
score of `a` is the number of pairwise contests `a` wins minus the number it loses; the
second-order score of `a` is the sum of the Copeland scores of the candidates `a` defeats. The
winner has the highest Copeland score, ties broken by the highest second-order score. So `p` is
the unique winner when every other candidate has a smaller Copeland score than `p`, or the same
Copeland score and a smaller second-order score.

This is Existence of a Winning Preference for second-order Copeland (Bartholdi, Tovey and
Trick, Theorem 3) in its unique-winner form. Their Section 3 question asks for a preference
that "will ensure that `c` will be the winner"; their hardness proof establishes the
unique-winner form: Theorem 3 reduces from Tournament Outcome, and the proof of Theorem 2 shows
that "there is a set of outcomes for the remaining contests `R` which will make `c` the unique
winner if-and-only-if the instance of 3,4-SAT is satisfiable". The co-winner form (`p` among
the winners) is not formalized here. Their Theorem 4 (a manipulator with given sincere
preferences and a fixed tie-breaking order among candidates) is also a different statement.

Pairwise majority is `MathlibExt.GameTheory.SocialChoice.CondorcetCycle.MajorityPrefers`
(strictly more than half of the voters strictly prefer `a` to `b`), on a profile of the shared
strict total orders `MathlibExt.Order.StrictTotalOrder`
(`MathlibExt.GameTheory.SocialChoice.ArrowWanted.Profile`). Strictly more than half preferring
`a` to `b` is the same as more voters preferring `a` to `b` than `b` to `a`, since every voter
ranks the two strictly.

Candidates are distinct natural numbers listed in `C`. A sincere vote is a list ordering the
candidates from most to least preferred, that is, a permutation of `C`. The election has the
`|V|` sincere voters, numbered in the order of `V`, plus the manipulator, the last voter; the
manipulator's order `P` is any strict total order on `C`. `V` is a list (a multiset: equal votes
may repeat).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the candidates `C`, the sincere votes `V` (each listing the candidates from
most to least preferred), and the distinguished candidate `p`. -/
abbrev SecondOrderCopelandManipulationInstance := List ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the candidates are distinct, every sincere vote is a
permutation of the candidates, and `p` is a candidate. -/
def WellFormed (i : SecondOrderCopelandManipulationInstance) : Prop :=
  i.1.Nodup ∧ (∀ v ∈ i.2.1, v.Perm i.1) ∧ i.2.2 ∈ i.1

/-- The candidates of an instance. -/
abbrev Candidate (i : SecondOrderCopelandManipulationInstance) : Type := {x : ℕ // x ∈ i.1}

open Classical in
/-- The Copeland score of `a`: the number of pairwise contests `a` wins minus the number it
loses. -/
noncomputable def copelandScore {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) : ℤ :=
  ((Finset.univ.filter fun b => MajorityPrefers P a b).card : ℤ) -
    ((Finset.univ.filter fun b => MajorityPrefers P b a).card : ℤ)

open Classical in
/-- The second-order Copeland score of `a`: the sum of the Copeland scores of the candidates
that `a` defeats. -/
noncomputable def secondOrderScore {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) : ℤ :=
  ∑ b ∈ Finset.univ.filter (fun b => MajorityPrefers P a b), copelandScore P b

/-- `p` is the unique second-order Copeland winner: every other candidate has a smaller
Copeland score, or the same Copeland score and a smaller second-order score. -/
def IsUniqueWinner {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (p : Alt) : Prop :=
  ∀ q, q ≠ p → copelandScore P q < copelandScore P p ∨
    (copelandScore P q = copelandScore P p ∧ secondOrderScore P q < secondOrderScore P p)

/-- Some order of the manipulator (the last voter) makes `p` the unique winner, the other
voters voting their sincere orders: voter `k` prefers `a` to `b` exactly when `a` comes before
`b` in the `k`-th vote. -/
def SecondOrderCopelandManipulationFeasible
    (i : SecondOrderCopelandManipulationInstance) : Prop :=
  ∃ hp : i.2.2 ∈ i.1, ∃ P : Profile (Candidate i) (Fin (i.2.1.length + 1)),
    (∀ k : Fin i.2.1.length, ∀ a b : Candidate i,
      (P k.castSucc).lt a b ↔ (i.2.1.get k).idxOf a.1 < (i.2.1.get k).idxOf b.1) ∧
    IsUniqueWinner P ⟨i.2.2, hp⟩

open Classical in
/-- SECOND-ORDER COPELAND MANIPULATION as a decision problem over bitstrings. -/
noncomputable def secondOrderCopelandManipulationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SecondOrderCopelandManipulationInstance) x with
  | some i => decide (WellFormed i ∧ SecondOrderCopelandManipulationFeasible i)
  | none => false

/-- **SECOND-ORDER COPELAND MANIPULATION (unique winner) is NP-complete.** Source: Bartholdi,
Tovey and Trick (1989), Theorems 2 and 3. -/
public theorem_wanted secondOrderCopelandManipulation_npComplete :
    secondOrderCopelandManipulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L secondOrderCopelandManipulationDec

end MetaMathlibExt.Complexity.NPComplete.SecondOrderCopelandManipulation
