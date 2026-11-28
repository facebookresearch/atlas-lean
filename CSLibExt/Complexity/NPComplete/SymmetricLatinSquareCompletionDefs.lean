/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SYMMETRIC LATIN SQUARE COMPLETION: definitions

Source:
C. J. Colbourn, "Embedding partial Steiner triple systems is NP-complete", Journal of
Combinatorial Theory, Series A 35 (1983), 100-105, doi:10.1016/0097-3165(83)90031-6 (abstract:
"In so doing, it is proved that deciding whether a partial commutative quasigroup can be completed
to a commutative quasigroup is NP-complete"; the full text was not available to us).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.LatinSquareCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SymmetricLatinSquareCompletion

open LatinSquareCompletion (LatinSquareCompletionInstance)

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

end MetaMathlibExt.Complexity.NPComplete.SymmetricLatinSquareCompletion
