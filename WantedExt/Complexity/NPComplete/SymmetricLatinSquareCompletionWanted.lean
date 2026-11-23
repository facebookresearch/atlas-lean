/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SYMMETRIC LATIN SQUARE COMPLETION is NP-complete

Source:
C. J. Colbourn, "Embedding partial Steiner triple systems is NP-complete", Journal of
Combinatorial Theory, Series A 35 (1983), 100-105, doi:10.1016/0097-3165(83)90031-6 (abstract:
"In so doing, it is proved that deciding whether a partial commutative quasigroup can be completed
to a commutative quasigroup is NP-complete"; the full text was not available to us).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.LatinSquareCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SymmetricLatinSquareCompletion

open LatinSquareCompletion (LatinSquareCompletionInstance)

/-!
# SYMMETRIC LATIN SQUARE COMPLETION is NP-complete

INSTANCE: a symmetric partial Latin square of order `n`, i.e. a partial commutative quasigroup:
an `n × n` array, some cells filled with symbols from `{1, …, n}`, no symbol repeated in a row or
a column, and the filled cells symmetric (cell `(r, c)` is filled exactly when `(c, r)` is, with
the same symbol). QUESTION: can the empty cells be filled to give a symmetric Latin square, i.e.
the table of a commutative quasigroup on `n` elements?

A quasigroup's operation table is a Latin square, and the operation is commutative exactly when
the table is symmetric. The instance type, the conventions (`0` for an empty cell, symbols
`1, …, n`, rows listed top to bottom) and the base well-formedness (`n > 0`, an `n × n` array of
entries at most `n`) are those of LATIN SQUARE COMPLETION (`LatinSquareCompletionWanted`), and
the question is that module's completion condition (every row and every column a permutation of
`1, …, n`, agreeing with the filled cells) with the completion also required to be symmetric;
that predicate hides its completion, so its conditions are restated verbatim and the symmetry
conjunct is added. This module adds to well-formedness the symmetry of the partial square and
the partial Latin condition (no symbol twice in a row; columns follow by symmetry).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The entry in row `r`, column `c` of an array of rows (`0` outside the array). -/
def entry (M : List (List ℕ)) (r c : ℕ) : ℕ := (M.getD r []).getD c 0

/-- Well-formedness of an instance: a well-formed LATIN SQUARE COMPLETION instance (`n > 0`, an
`n × n` array with entries at most `n`) that is symmetric and has no filled symbol twice in a row.
-/
def WellFormed (i : LatinSquareCompletionInstance) : Prop :=
  LatinSquareCompletion.WellFormed i ∧
    (∀ r < i.1, ∀ c < i.1, entry i.2 r c = entry i.2 c r) ∧
    ∀ r < i.1, ∀ c < i.1, ∀ c' < i.1, c ≠ c' → entry i.2 r c ≠ 0 →
      entry i.2 r c ≠ entry i.2 r c'

/-- A completion as in `LatinSquareCompletion.LatinSquareCompletionFeasible` (every row and
column a permutation of `1, …, n`, agreeing with the filled cells) that is also symmetric. -/
def SymmetricLatinSquareCompletionFeasible (i : LatinSquareCompletionInstance) : Prop :=
  ∃ completion : List (List ℕ), completion.length = i.1 ∧
    (∀ row ∈ completion, row.length = i.1) ∧
    (∀ r < i.1, ∀ c < i.1, (i.2.getD r []).getD c 0 = 0 ∨
      (i.2.getD r []).getD c 0 = (completion.getD r []).getD c 0) ∧
    (∀ r < i.1, (completion.getD r []).Perm ((List.range i.1).map (· + 1))) ∧
    (∀ c < i.1, ((List.range i.1).map
      (fun r => (completion.getD r []).getD c 0)).Perm ((List.range i.1).map (· + 1))) ∧
    ∀ r < i.1, ∀ c < i.1, entry completion r c = entry completion c r

open Classical in
/-- SYMMETRIC LATIN SQUARE COMPLETION as a decision problem over bitstrings. -/
noncomputable def symmetricLatinSquareCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LatinSquareCompletionInstance) x with
  | some i => decide (WellFormed i ∧ SymmetricLatinSquareCompletionFeasible i)
  | none => false

/-- **SYMMETRIC LATIN SQUARE COMPLETION is NP-complete.** Source: Colbourn (1983). -/
public theorem_wanted symmetricLatinSquareCompletion_npComplete :
    symmetricLatinSquareCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L symmetricLatinSquareCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SymmetricLatinSquareCompletion
