/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHAMBERLIN-COURANT WINNER DETERMINATION is NP-complete

Source:
T. Lu and C. Boutilier, "Budgeted social choice: From consensus to personalized decision
making", Proceedings of the 22nd International Joint Conference on Artificial Intelligence
(IJCAI 2011), 280-286, https://www.ijcai.org/Proceedings/11/Papers/057.pdf, Theorem 8
(stated for the Borda score `∑ᵥ maxₐ (m - 1 - posᵥ(a)) ≥ t`, which is the bound
`B = n (m - 1) - t` on the misrepresentation below);
N. Betzler, A. Slinko, and J. Uhlmann, "On the computation of fully proportional
representation", Journal of Artificial Intelligence Research 47 (2013), 475-519,
doi:10.1613/jair.3896, Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChamberlinCourantWinnerDetermination

/-!
# CHAMBERLIN-COURANT WINNER DETERMINATION is NP-complete

INSTANCE: a set `C` of candidates, a list of voters, each with a strict ranking of `C`, a
committee size `k`, and a misrepresentation bound `B`. QUESTION: is there a committee `W ⊆ C` of
`k` candidates such that the total Borda misrepresentation, the sum over the voters of the
position (`0` for the top choice, `|C| - 1` for the last) of their best-ranked member of `W`, is
at most `B`?

Representation. The candidates are `C = {0, ..., m - 1}`. A vote is a list of candidates, best
first, listing every candidate exactly once (`List.Perm` of `List.range m`); the position of
`c` in vote `v` is `v.idxOf c`, the Borda misrepresentation `(0, 1, ..., m - 1)`. The question
is stated with an assignment `r` of a representative in `W` to each voter: the minimum over
assignments of the total misrepresentation is the sum of the voters' misrepresentations by their
best-ranked members of `W`, so the two readings agree. As in Lu and Boutilier's
`K`-recommendation sets, a committee member need not represent any voter.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of candidates, the votes, the committee size `k`, and the bound
`B`. -/
abbrev ChamberlinCourantWinnerDeterminationInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every vote is a strict ranking of all `m` candidates, and
the committee size satisfies `0 < k ≤ m`. -/
def WellFormed (i : ChamberlinCourantWinnerDeterminationInstance) : Prop :=
  (∀ v ∈ i.2.1, v.Perm (List.range i.1)) ∧ 0 < i.2.2.1 ∧ i.2.2.1 ≤ i.1

/-- A committee `W` of `k` candidates and an assignment `r` of a representative in `W` to each
voter whose total Borda misrepresentation is at most `B`. -/
def ChamberlinCourantWinnerDeterminationFeasible
    (i : ChamberlinCourantWinnerDeterminationInstance) : Prop :=
  ∃ W : Finset (Fin i.1), W.card = i.2.2.1 ∧
    ∃ r : Fin i.2.1.length → Fin i.1, (∀ j, r j ∈ W) ∧
      ∑ j : Fin i.2.1.length, i.2.1[j].idxOf (r j : ℕ) ≤ i.2.2.2

open Classical in
/-- CHAMBERLIN-COURANT WINNER DETERMINATION as a decision problem over bitstrings. -/
noncomputable def chamberlinCourantWinnerDeterminationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChamberlinCourantWinnerDeterminationInstance) x with
  | some i => decide (WellFormed i ∧ ChamberlinCourantWinnerDeterminationFeasible i)
  | none => false

/-- **CHAMBERLIN-COURANT WINNER DETERMINATION is NP-complete** (Borda misrepresentation).
Source: Lu and Boutilier (2011), Theorem 8; Betzler, Slinko, and Uhlmann (2013), Theorem 2. -/
public theorem_wanted chamberlinCourantWinnerDetermination_npComplete :
    chamberlinCourantWinnerDeterminationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chamberlinCourantWinnerDeterminationDec

end MetaMathlibExt.Complexity.NPComplete.ChamberlinCourantWinnerDetermination
