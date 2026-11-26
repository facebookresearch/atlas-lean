/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL LATIN SQUARE: ANOTHER COMPLETION is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 397-411,
doi:10.1016/0196-6774(83)90019-6, problem [2] PARTIAL LATIN SQUARE EXTENDABILITY, comment;
C. J. Colbourn, M. J. Colbourn and D. R. Stinson, "The computational complexity of recognizing
critical sets", Graph Theory Singapore 1983, Lecture Notes in Mathematics 1073 (1984), 248-253,
doi:10.1007/BFb0073124.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.LatinSquareCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialLatinSquareAnotherCompletion

/-!
# PARTIAL LATIN SQUARE: ANOTHER COMPLETION is NP-complete

Johnson's column states PARTIAL LATIN SQUARE EXTENDABILITY (INSTANCE: an `n × n` matrix `M`
with entries from `{0, 1, …, n}` such that no row or column contains a repeated entry other than
`0`; QUESTION: can `M` be extended to a full Latin square, i.e. can each `0` entry be replaced by
a member of `{1, …, n}` so that no row or column contains a repeated entry?) and comments that
"the question of whether `M` has more than one completion to a Latin square (even when given the
first as part of the input)" is also NP-complete, citing Colbourn, Colbourn and Stinson. This is
the version with the first completion given:

INSTANCE: an `n × n` partial Latin square `M` and a completion `L` of `M` to a Latin square.
QUESTION: does `M` have a completion to a Latin square different from `L`?

The matrix part reuses `LatinSquareCompletion`: `n` and `M`, row by row, with `0` for a missing
entry. A completion of `M` is a full `n × n` matrix `C` (entries in `1, …, n`) that agrees with
`M` on its nonzero entries and is a Latin square. Being a Latin square is expressed with
`LatinSquareCompletion.LatinSquareCompletionFeasible`: a full matrix's only completion is the
matrix itself, so `(n, C)` is a yes-instance of `LATIN SQUARE COMPLETION` exactly when every row
and column of `C` is a permutation of `1, …, n`. `WellFormed` asks for
`LatinSquareCompletion.WellFormed` and that `L` completes `M`; `M` then has no repeated nonzero
entry in a row or column, since the Latin square `L` extends it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PARTIAL LATIN SQUARE: ANOTHER COMPLETION is NP-complete.** Source: Johnson (1983),
problem [2], comment; Colbourn, Colbourn and Stinson (1984). -/
public theorem_wanted partialLatinSquareAnotherCompletion_npComplete :
    partialLatinSquareAnotherCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partialLatinSquareAnotherCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PartialLatinSquareAnotherCompletion
