/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LOBBYING IN MULTIPLE REFERENDA is NP-complete

Source:
R. Christian, M. Fellows, F. Rosamond, and A. Slinko, "On complexity of lobbying in multiple
referenda", Review of Economic Design 11(3) (2007), 217-224, doi:10.1007/s10058-007-0028-1
(OPTIMAL LOBBYING is W[2]-complete for the parameter `b`, hence NP-hard);
problem statement as restated by G. Erdélyi, H. Fernau, J. Goldsmith, N. Mattei, D. Raible,
and J. Rothe, "The complexity of probabilistic lobbying", arXiv:0906.4431 (Section 1.1,
OPTIMAL LOBBYING; Section 4.2: the W[2]-hardness "implies NP-hardness of OL").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LobbyingInMultipleReferenda

/-!
# LOBBYING IN MULTIPLE REFERENDA is NP-complete

OPTIMAL LOBBYING. INSTANCE: an `m × n` 0/1 matrix `E`, each row a voter and each column an issue
(entry `1` if the voter votes "yes" on the issue), a 0/1 target vector `Z` of length `n` (the
lobby's desired outcome), and a positive integer `b`. QUESTION: is there a choice of `b` rows of
`E` (`b` voters) that can be changed so that in each column of the resulting matrix a strict
majority vote yields the outcome targeted by the lobby?

A strict majority vote on an issue yields "yes" when more than half of the `m` voters vote
"yes" (`m < 2 · #yes`), and "no" otherwise. The matrix is given by its rows, each a list of `n`
Booleans, so the instance lists all `m · n` entries; "a choice of `b` rows" presupposes
`b ≤ m`, which `WellFormed` records.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the matrix `E` (row `r` lists voter `r`'s votes on the issues),
the target vector `Z`, and the number `b` of voters to change. -/
abbrev LobbyingInMultipleReferendaInstance := List (List Bool) × List Bool × ℕ

/-- The voters of the instance, one per row. -/
abbrev Voter (i : LobbyingInMultipleReferendaInstance) : Type := Fin i.1.length

/-- The issues of the instance, one per entry of the target vector. -/
abbrev Issue (i : LobbyingInMultipleReferendaInstance) : Type := Fin i.2.1.length

/-- The entry `E[r][j]`: voter `r`'s vote on issue `j`. -/
def vote (i : LobbyingInMultipleReferendaInstance) (r : Voter i) (j : Issue i) : Bool :=
  (i.1.get r).getD j false

/-- The lobby's target outcome `Z[j]` on issue `j`. -/
def target (i : LobbyingInMultipleReferendaInstance) (j : Issue i) : Bool :=
  i.2.1.get j

/-- The strict majority outcome of issue `j` under the votes `F`: "yes" iff more than half of
the voters vote "yes". -/
def majorityOutcome {m n : ℕ} (F : Fin m → Fin n → Bool) (j : Fin n) : Bool :=
  decide (m < 2 * (Finset.univ.filter fun r => F r j = true).card)

/-- Well-formedness of an instance: every row has one entry per issue, and `0 < b ≤ m`. -/
def WellFormed (i : LobbyingInMultipleReferendaInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.2.1.length) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1.length

/-- Some choice of `b` rows can be changed so that every issue's strict majority outcome is the
target: a set `S` of `b` voters and new votes `F` agreeing with `E` outside `S`. -/
def LobbyingInMultipleReferendaFeasible (i : LobbyingInMultipleReferendaInstance) : Prop :=
  ∃ S : Finset (Voter i), S.card = i.2.2 ∧
    ∃ F : Voter i → Issue i → Bool, (∀ r, r ∉ S → ∀ j, F r j = vote i r j) ∧
      ∀ j, majorityOutcome F j = target i j

open Classical in
/-- LOBBYING IN MULTIPLE REFERENDA as a decision problem over bitstrings. -/
noncomputable def lobbyingInMultipleReferendaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LobbyingInMultipleReferendaInstance) x with
  | some i => decide (WellFormed i ∧ LobbyingInMultipleReferendaFeasible i)
  | none => false

/-- **LOBBYING IN MULTIPLE REFERENDA is NP-complete.** Source: Christian, Fellows, Rosamond,
and Slinko (2007); Erdélyi, Fernau, Goldsmith, Mattei, Raible, and Rothe (arXiv:0906.4431). -/
public theorem_wanted lobbyingInMultipleReferenda_npComplete :
    lobbyingInMultipleReferendaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lobbyingInMultipleReferendaDec

end MetaMathlibExt.Complexity.NPComplete.LobbyingInMultipleReferenda
