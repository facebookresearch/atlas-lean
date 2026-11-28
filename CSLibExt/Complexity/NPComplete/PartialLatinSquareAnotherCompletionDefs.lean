/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL LATIN SQUARE: ANOTHER COMPLETION: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 397-411,
doi:10.1016/0196-6774(83)90019-6, problem [2] PARTIAL LATIN SQUARE EXTENDABILITY, comment;
C. J. Colbourn, M. J. Colbourn and D. R. Stinson, "The computational complexity of recognizing
critical sets", Graph Theory Singapore 1983, Lecture Notes in Mathematics 1073 (1984), 248-253,
doi:10.1007/BFb0073124.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.LatinSquareCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialLatinSquareAnotherCompletion



open LatinSquareCompletion

/-- An instance: the size `n` and the partial Latin square `M` (`0` = missing entry), and the
given completion `L`. -/
abbrev PartialLatinSquareAnotherCompletionInstance :=
  LatinSquareCompletionInstance × List (List ℕ)

/-- The entry in row `r`, column `c` of a matrix given row by row (`0` outside it). -/
def entry (A : List (List ℕ)) (r c : ℕ) : ℕ := (A.getD r []).getD c 0

/-- `C` completes `M` to a Latin square: `C` is a full `n × n` matrix with entries in
`1, …, n`, it agrees with `M` on the nonzero entries of `M`, and it is a Latin square (as a full
matrix it is a yes-instance of `LATIN SQUARE COMPLETION`). -/
def IsCompletion (i : LatinSquareCompletionInstance) (C : List (List ℕ)) : Prop :=
  LatinSquareCompletion.WellFormed (i.1, C) ∧ (∀ r < i.1, ∀ c < i.1, entry C r c ≠ 0) ∧
    (∀ r < i.1, ∀ c < i.1, entry i.2 r c = 0 ∨ entry i.2 r c = entry C r c) ∧
    LatinSquareCompletionFeasible (i.1, C)

/-- Well-formedness: `(n, M)` is a well-formed `LATIN SQUARE COMPLETION` instance and `L`
completes `M`. -/
def WellFormed (i : PartialLatinSquareAnotherCompletionInstance) : Prop :=
  LatinSquareCompletion.WellFormed i.1 ∧ IsCompletion i.1 i.2

/-- `M` has a completion different from `L`. -/
def PartialLatinSquareAnotherCompletionFeasible
    (i : PartialLatinSquareAnotherCompletionInstance) : Prop :=
  ∃ C, IsCompletion i.1 C ∧ C ≠ i.2

open Classical in
/-- PARTIAL LATIN SQUARE: ANOTHER COMPLETION as a decision problem over bitstrings. -/
noncomputable def partialLatinSquareAnotherCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartialLatinSquareAnotherCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PartialLatinSquareAnotherCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialLatinSquareAnotherCompletion
