/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DODGSON SCORE is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "Voting schemes for which it can be difficult
to tell who won the election", Social Choice and Welfare 6 (1989), 157-165,
doi:10.1007/BF00303169;
E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Exact analysis of Dodgson elections: Lewis
Carroll's 1876 voting system is complete for parallel access to NP", Journal of the ACM 44
(1997), 806-825, doi:10.1145/268999.269002 (arXiv:cs/9907036), Section 3 (the decision problem
DodgsonScore and its NP-completeness, due to Bartholdi, Tovey and Trick).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DodgsonScore

open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers)

/-!
# DODGSON SCORE is NP-complete

INSTANCE: a set `C` of candidates, a candidate `c ∈ C`, a multiset `V` of voters' preference
orders on `C` (strict, transitive and complete; coded as a list), and a positive integer `k`.
QUESTION: is the Dodgson score of `c` at most `k`, i.e., can `c` be made a Condorcet winner by at
most `k` sequential switches, where a switch exchanges two adjacent candidates in one voter's
preference order, and a Condorcet winner is preferred to each other candidate by strictly more
than half of the voters?

Candidates are `0, …, m - 1`, and each voter's preference order is a list of all candidates,
each once, most preferred first. A switch `(v, p)` exchanges the candidates at positions `p` and
`p + 1` of voter `v`'s list. The resulting lists are read as a profile of strict total orders
(`MathlibExt`'s `Profile`, the encoding of Arrow's theorem), and pairwise majority is
`MathlibExt`'s `MajorityPrefers` (strictly more than half of the voters strictly prefer one
candidate to the other). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of candidates `m`, the candidate `c`, the voters' preference lists
(most preferred first), and the bound `k`. -/
abbrev DodgsonScoreInstance := ℕ × ℕ × List (List ℕ) × ℕ

/-- Exchange the entries at positions `p` and `p + 1` of a preference list. -/
def switchAt (l : List ℕ) (p : ℕ) : List ℕ :=
  (l.set p (l.getD (p + 1) 0)).set (p + 1) (l.getD p 0)

/-- Apply the switch `(v, p)`: exchange the candidates at positions `p` and `p + 1` of voter
`v`'s preference list. -/
def applySwitch (V : List (List ℕ)) (s : ℕ × ℕ) : List (List ℕ) :=
  V.set s.1 (switchAt (V.getD s.1 []) s.2)

/-- `c` is a Condorcet winner for the preference lists `V` over `m` candidates: the lists are
the orders of a profile `R` (voter `v` strictly prefers `a` to `b` exactly when `a` comes before
`b` in `v`'s list), and in `R` the candidate `c` beats every other candidate by pairwise
majority. -/
def IsCondorcetWinner (m : ℕ) (V : List (List ℕ)) (c : ℕ) : Prop :=
  ∃ R : Profile (Fin m) (Fin V.length),
    (∀ v a b, (R v).lt a b ↔ (V.get v).idxOf a.1 < (V.get v).idxOf b.1) ∧
      ∀ a d : Fin m, a.1 = c → d ≠ a → MajorityPrefers R a d

/-- Well-formedness of an instance: `c` is a candidate, every voter's list contains every
candidate exactly once, and `k` is positive. -/
def WellFormed (i : DodgsonScoreInstance) : Prop :=
  i.2.1 < i.1 ∧ (∀ l ∈ i.2.2.1, l.Perm (List.range i.1)) ∧ 0 < i.2.2.2

/-- At most `k` switches of adjacent candidates make `c` a Condorcet winner. -/
def DodgsonScoreFeasible (i : DodgsonScoreInstance) : Prop :=
  ∃ S : List (ℕ × ℕ), S.length ≤ i.2.2.2 ∧
    (∀ s ∈ S, s.1 < i.2.2.1.length ∧ s.2 + 1 < i.1) ∧
      IsCondorcetWinner i.1 (S.foldl applySwitch i.2.2.1) i.2.1

open Classical in
/-- DODGSON SCORE as a decision problem over bitstrings. -/
noncomputable def dodgsonScoreDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DodgsonScoreInstance) x with
  | some i => decide (WellFormed i ∧ DodgsonScoreFeasible i)
  | none => false

/-- **DODGSON SCORE is NP-complete.** Source: Bartholdi, Tovey and Trick (1989); Hemaspaandra,
Hemaspaandra and Rothe (1997), Section 3. -/
public theorem_wanted dodgsonScore_npComplete :
    dodgsonScoreDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dodgsonScoreDec

end MetaMathlibExt.Complexity.NPComplete.DodgsonScore
