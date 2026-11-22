/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR ORDERING (TOURNAMENTS) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LINEAR ORDERING; N. Alon,
"Ranking tournaments" (2006) and the feedback arc set literature.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearOrderingTournament

/-!
# LINEAR ORDERING (TOURNAMENTS) is NP-complete

A tournament (for every distinct pair of vertices exactly one direction is an edge) and a bound
`K`. The question is whether some vertex ordering has at least `K` forward arcs, witnessed by a
sublist of at least `K` forward edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A tournament linear-ordering instance: vertex count, tournament edges, bound. -/
abbrev LinearOrderingTournamentInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : LinearOrderingTournamentInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ∀ a < i.1, ∀ b < i.1, a ≠ b → (a, b) ∈ i.2.1 ∨ (b, a) ∈ i.2.1

/-- An ordering with at least `K` forward arcs. -/
def LinearOrderingTournamentFeasible
    (i : LinearOrderingTournamentInstance) : Prop :=
  ∃ ord : List ℕ, ord.Perm (List.range i.1) ∧
    ∃ forward : List (ℕ × ℕ), forward.Sublist i.2.1 ∧ i.2.2 ≤ forward.length ∧
      ∀ e ∈ forward, ord.idxOf e.1 < ord.idxOf e.2

open Classical in
/-- LINEAR ORDERING (TOURNAMENTS) as a decision problem over bitstrings. -/
noncomputable def linearOrderingTournamentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LinearOrderingTournamentInstance) x with
  | some i => decide (WellFormed i ∧ LinearOrderingTournamentFeasible i)
  | none => false

/-- **LINEAR ORDERING (TOURNAMENTS) is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), LINEAR ORDERING; N. Alon, "Ranking tournaments"
(2006) and the feedback arc set literature. -/
public theorem_wanted linearOrderingTournament_npComplete :
    linearOrderingTournamentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearOrderingTournamentDec

end MetaMathlibExt.Complexity.NPComplete.LinearOrderingTournament
