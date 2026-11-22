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

/-- **Tournament linear ordering instances.** An instance of LINEAR ORDERING (TOURNAMENTS) is a
triple $(n, E, K)$ of a natural number $n$, the number of vertices, a list $E$ of ordered pairs
of natural numbers, the arcs, and a natural number $K$, the bound. -/
abbrev LinearOrderingTournamentInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed tournament linear ordering instances.** An instance $(n, E, K)$ of LINEAR
ORDERING (TOURNAMENTS) is well formed when $n > 0$, $E$ has no repeated entries, every pair
$(a, b)$ in $E$ satisfies $a < n$, $b < n$, $a \ne b$ and $(b, a) \notin E$, and for all distinct
$a, b < n$ at least one of $(a, b)$ and $(b, a)$ lies in $E$. That is, $E$ is a tournament on the
vertices $0, \dots, n - 1$. -/
def WellFormed (i : LinearOrderingTournamentInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ∀ a < i.1, ∀ b < i.1, a ≠ b → (a, b) ∈ i.2.1 ∨ (b, a) ∈ i.2.1

/-- **Orderings with many forward arcs.** An instance $(n, E, K)$ of LINEAR ORDERING
(TOURNAMENTS) is feasible when there are an ordering of the vertices $0, \dots, n - 1$ and a
subsequence $F$ of the list $E$ with at least $K$ entries such that for every pair $(a, b)$ in
$F$, the position of $a$ in the ordering is less than the position of $b$, where positions are
counted from $0$ and a number that does not occur in the ordering is given position $n$. -/
def LinearOrderingTournamentFeasible
    (i : LinearOrderingTournamentInstance) : Prop :=
  ∃ ord : List ℕ, ord.Perm (List.range i.1) ∧
    ∃ forward : List (ℕ × ℕ), forward.Sublist i.2.1 ∧ i.2.2 ≤ forward.length ∧
      ∀ e ∈ forward, ord.idxOf e.1 < ord.idxOf e.2

open Classical in
/-- **LINEAR ORDERING (TOURNAMENTS) as a decision problem.** The decision problem LINEAR
ORDERING (TOURNAMENTS) accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of triples of a natural number, a list of pairs of natural numbers and a
natural number, to an instance $(n, E, K)$ that is well formed ($n > 0$ and $E$ is a tournament
on the vertices $0, \dots, n - 1$ without repeated arcs) and feasible (some ordering of the
vertices has at least $K$ arcs of $E$ going forward). Bitstrings that do not decode, or that
decode to a malformed instance, are rejected. -/
noncomputable def linearOrderingTournamentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LinearOrderingTournamentInstance) x with
  | some i => decide (WellFormed i ∧ LinearOrderingTournamentFeasible i)
  | none => false

/-- **LINEAR ORDERING (TOURNAMENTS) is NP-complete.** The decision problem LINEAR ORDERING
(TOURNAMENTS) on bitstrings lies in NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), LINEAR ORDERING; N. Alon, "Ranking tournaments"
(2006) and the feedback arc set literature. -/
public theorem_wanted linearOrderingTournament_npComplete :
    linearOrderingTournamentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearOrderingTournamentDec

end MetaMathlibExt.Complexity.NPComplete.LinearOrderingTournament
