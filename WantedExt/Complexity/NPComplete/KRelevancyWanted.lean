/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-RELEVANCY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MP7] K-RELEVANCY, p. 246, crediting
S. P. Reiss and D. P. Dobkin, "The complexity of linear programming", Report No. 69, Dept. of
Computer Science, Yale University (1976) (transformation from X3C; NP-complete in the strong
sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Finset.Card
public import WantedExt.Complexity.NPComplete.IntegerProgrammingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KRelevancy

open MetaMathlibExt.Complexity.NPComplete.IntegerProgramming (toInt)

/-!
# K-RELEVANCY is NP-complete

INSTANCE: a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of integers and `b` is an
integer, and a positive integer `K ≤ |X|`.
QUESTION: is there a subset `X' ⊆ X` with `|X'| ≤ K` such that, for all `m`-tuples `y` of
rational numbers, if `x · y ≤ b` for all `(x, b) ∈ X'`, then `x · y ≤ b` for all `(x, b) ∈ X`?

`X` is a list of constraints in the encoding of INTEGER PROGRAMMING (`IntegerProgramming.toInt`
reads an integer from a `(positive part, negative part)` pair); `WellFormed` asks the decoded
constraints to be pairwise distinct, so the list is a set and its length is `|X|`. A subset
`X'` is a set of positions in the list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the dimension `m`, the constraint pairs `(x, b)` (entries as `(positive part,
negative part)` pairs), and the bound `K`. -/
abbrev KRelevancyInstance := ℕ × List (List (ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- The rational point `y` satisfies the constraint `x · y ≤ b`. -/
def Satisfies {m : ℕ} (xb : List (ℕ × ℕ) × (ℕ × ℕ)) (y : Fin m → ℚ) : Prop :=
  ∑ j : Fin m, (toInt (xb.1.getD j (0, 0)) : ℚ) * y j ≤ toInt xb.2

/-- Well-formedness of an instance: every tuple has length `m`, the decoded constraints are
pairwise distinct, and `0 < K ≤ |X|`. -/
def WellFormed (i : KRelevancyInstance) : Prop :=
  (∀ xb ∈ i.2.1, xb.1.length = i.1) ∧
    (i.2.1.map fun xb => (xb.1.map toInt, toInt xb.2)).Nodup ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A subset `X'` of at most `K` of the listed constraints (chosen by position) whose solutions
over `ℚ^m` all satisfy every constraint of `X`. -/
def KRelevancyFeasible (i : KRelevancyInstance) : Prop :=
  ∃ S : Finset (Fin i.2.1.length), S.card ≤ i.2.2 ∧
    ∀ y : Fin i.1 → ℚ, (∀ k ∈ S, Satisfies (i.2.1.get k) y) → ∀ k, Satisfies (i.2.1.get k) y

open Classical in
/-- K-RELEVANCY as a decision problem over bitstrings. -/
noncomputable def kRelevancyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KRelevancyInstance) x with
  | some i => decide (WellFormed i ∧ KRelevancyFeasible i)
  | none => false

/-- **K-RELEVANCY is NP-complete.** Source: Garey and Johnson (1979), [MP7]; Reiss and Dobkin
(1976). -/
public theorem_wanted kRelevancy_npComplete :
    kRelevancyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kRelevancyDec

end MetaMathlibExt.Complexity.NPComplete.KRelevancy
