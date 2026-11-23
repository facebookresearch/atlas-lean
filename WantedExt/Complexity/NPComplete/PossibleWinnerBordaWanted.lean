/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POSSIBLE WINNER for Borda is NP-complete

Source:
L. Xia and V. Conitzer, "Determining possible and necessary winners given partial orders",
Journal of Artificial Intelligence Research 41 (2011), 25-67, doi:10.1613/jair.3186
(arXiv:1401.3876), Section 2 (Borda), Definitions 1-2 (extensions, possible winner) and
Theorem 1 (possible winner is NP-complete for positional scoring rules including Borda);
N. Betzler and B. Dorn, "Towards a dichotomy for the possible winner problem in elections based
on scoring rules", Journal of Computer and System Sciences 76 (2010), 812-836,
doi:10.1016/j.jcss.2010.04.002.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PossibleWinnerBorda

/-!
# POSSIBLE WINNER for Borda is NP-complete

INSTANCE: a set `C` of `m` alternatives, a profile `(O₁, …, Oₙ)` of partial orders on `C`, and an
alternative `c ∈ C`. QUESTION: is `c` a possible winner with respect to Borda, i.e., is there a
profile `(V₁, …, Vₙ)` of linear orders such that each `Vᵢ` extends `Oᵢ` (`a ≻_{Oᵢ} b` implies
`a ≻_{Vᵢ} b`) and Borda selects exactly `c`?

Borda is the positional scoring rule with scoring vector `(m - 1, m - 2, …, 0)`: an alternative
ranked in position `j` (counting from 0) of a vote gets `m - 1 - j` points, its score is the sum
over the votes, and the rule selects the alternatives of maximum score; it selects exactly `c`
when `c`'s score exceeds every other alternative's. The alternatives are listed explicitly (a list
`C` of distinct names, so the input lists every alternative); a partial order is the list of its
pairs `(a, b)` with `a ≻ b`, required to name alternatives and to be a strict partial order
(Mathlib's `IsStrictOrder`); a linear order is a list of all alternatives, each once, most
preferred first. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the alternatives `C`, the partial orders (each the list of its pairs `(a, b)`
with `a ≻ b`), and the alternative `c`. -/
abbrev PossibleWinnerBordaInstance := List ℕ × List (List (ℕ × ℕ)) × ℕ

/-- The voters of the instance, `Fin n` for `n` listed partial orders. -/
abbrev Voter (i : PossibleWinnerBordaInstance) : Type := Fin i.2.1.length

/-- Voter `v`'s partial order: `a ≻ b` when `(a, b)` is listed. -/
def Pref (i : PossibleWinnerBordaInstance) (v : Voter i) (a b : ℕ) : Prop :=
  (a, b) ∈ i.2.1.get v

/-- The Borda score of `a` when voter `v` casts the linear order `P v`: the sum over the votes of
`m - 1 - (position of a)`, for `m = |C|` alternatives. -/
def bordaScore (i : PossibleWinnerBordaInstance) (P : Voter i → List ℕ) (a : ℕ) : ℕ :=
  ∑ v, (i.1.length - 1 - (P v).idxOf a)

/-- Well-formedness of an instance: the alternatives are distinct, `c` is an alternative, every
listed pair names two alternatives, and every voter's pairs form a strict partial order. -/
def WellFormed (i : PossibleWinnerBordaInstance) : Prop :=
  i.1.Nodup ∧ i.2.2 ∈ i.1 ∧ (∀ O ∈ i.2.1, ∀ q ∈ O, q.1 ∈ i.1 ∧ q.2 ∈ i.1) ∧
    ∀ v, IsStrictOrder ℕ (Pref i v)

/-- Some profile of linear orders extending the partial orders makes `c` the unique Borda
winner. -/
def PossibleWinnerBordaFeasible (i : PossibleWinnerBordaInstance) : Prop :=
  ∃ P : Voter i → List ℕ, (∀ v, (P v).Perm i.1) ∧
    (∀ v a b, Pref i v a b → (P v).idxOf a < (P v).idxOf b) ∧
    ∀ a ∈ i.1, a ≠ i.2.2 → bordaScore i P a < bordaScore i P i.2.2

open Classical in
/-- POSSIBLE WINNER for Borda as a decision problem over bitstrings. -/
noncomputable def possibleWinnerBordaDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x =>
    match MetaMathlibExt.BitstringEncoding.bitDecode (α := PossibleWinnerBordaInstance) x with
    | some i => decide (WellFormed i ∧ PossibleWinnerBordaFeasible i)
    | none => false

/-- **POSSIBLE WINNER for Borda is NP-complete.** Source: Xia and Conitzer (2011), Theorem 1;
Betzler and Dorn (2010). -/
public theorem_wanted possibleWinnerBorda_npComplete :
    possibleWinnerBordaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L possibleWinnerBordaDec

end MetaMathlibExt.Complexity.NPComplete.PossibleWinnerBorda
