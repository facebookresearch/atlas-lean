/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LATIN SQUARE COMPLETION is NP-complete

Source:
C. J. Colbourn, "The complexity of completing partial Latin squares" (1984).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LatinSquareCompletion

/-!
# LATIN SQUARE COMPLETION is NP-complete

A partial Latin square: an `n` by `n` grid with entries `0` (blank) through `n`. The question
is whether it can be completed so that every row and column is a permutation of `1, …, n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A Latin-square-completion instance: size n, partial grid (0 blank). -/
abbrev LatinSquareCompletionInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance. -/
def WellFormed (i : LatinSquareCompletionInstance) : Prop :=
  0 < i.1 ∧ i.2.length = i.1 ∧ (∀ row ∈ i.2, row.length = i.1) ∧
    ∀ row ∈ i.2, ∀ x ∈ row, x ≤ i.1

/-- A completion with every row and column a permutation. -/
def LatinSquareCompletionFeasible
    (i : LatinSquareCompletionInstance) : Prop :=
  ∃ completion : List (List ℕ), completion.length = i.1 ∧
    (∀ row ∈ completion, row.length = i.1) ∧
    (∀ r < i.1, ∀ c < i.1, (i.2.getD r []).getD c 0 = 0 ∨
      (i.2.getD r []).getD c 0 = (completion.getD r []).getD c 0) ∧
    (∀ r < i.1, (completion.getD r []).Perm ((List.range i.1).map (· + 1))) ∧
    ∀ c < i.1, ((List.range i.1).map
      (fun r => (completion.getD r []).getD c 0)).Perm ((List.range i.1).map (· + 1))

open Classical in
/-- LATIN SQUARE COMPLETION as a decision problem over bitstrings. -/
noncomputable def latinSquareCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LatinSquareCompletionInstance) x with
  | some i => decide (WellFormed i ∧ LatinSquareCompletionFeasible i)
  | none => false

/-- **LATIN SQUARE COMPLETION is NP-complete.** Source: C. J. Colbourn, "The complexity of
completing partial Latin squares" (1984). -/
public theorem_wanted latinSquareCompletion_npComplete :
    latinSquareCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L latinSquareCompletionDec

end MetaMathlibExt.Complexity.NPComplete.LatinSquareCompletion
