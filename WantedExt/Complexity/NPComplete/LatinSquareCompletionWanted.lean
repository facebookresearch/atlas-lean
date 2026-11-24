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

/-- **Latin square completion instances.** An instance of LATIN SQUARE COMPLETION is a pair
$(n, G)$ of a natural number $n$, the intended size, and a list $G$ of lists of natural numbers,
read as the rows of a partial grid in which the entry $0$ marks a blank cell. -/
abbrev LatinSquareCompletionInstance := ℕ × List (List ℕ)

/-- **Well-formed Latin square completion instances.** An instance $(n, G)$ of LATIN SQUARE
COMPLETION is well formed when $n > 0$, $G$ has exactly $n$ rows, every row of $G$ has length
$n$, and every entry of $G$ is at most $n$. -/
def WellFormed (i : LatinSquareCompletionInstance) : Prop :=
  0 < i.1 ∧ i.2.length = i.1 ∧ (∀ row ∈ i.2, row.length = i.1) ∧
    ∀ row ∈ i.2, ∀ x ∈ row, x ≤ i.1

/-- **Completable partial Latin squares.** An instance $(n, G)$ of LATIN SQUARE COMPLETION is
feasible when there is a grid $C$ consisting of $n$ rows of length $n$ such that for all
$r, c < n$ the entry $G_{rc}$ is either $0$ or equal to $C_{rc}$, every row of $C$ is a
permutation of $1, \dots, n$, and every column of $C$ is a permutation of $1, \dots, n$. Here
$G_{rc}$ is taken to be $0$ when $G$ has no entry in row $r$ and column $c$. -/
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
/-- **LATIN SQUARE COMPLETION as a decision problem.** The decision problem LATIN SQUARE
COMPLETION accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of pairs of a natural number and a list of lists of natural numbers, to an instance
$(n, G)$ that is well formed ($n > 0$ and $G$ consists of $n$ rows of length $n$ with entries at
most $n$) and feasible ($G$ can be completed to an $n \times n$ grid whose rows and columns are
permutations of $1, \dots, n$ and which agrees with $G$ on its nonzero entries). Bitstrings that
do not decode, or that decode to a malformed instance, are rejected. -/
noncomputable def latinSquareCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LatinSquareCompletionInstance) x with
  | some i => decide (WellFormed i ∧ LatinSquareCompletionFeasible i)
  | none => false

/-- **LATIN SQUARE COMPLETION is NP-complete.** The decision problem LATIN SQUARE COMPLETION on
bitstrings lies in NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

Source: C. J. Colbourn, "The complexity of
completing partial Latin squares" (1984). -/
public theorem_wanted latinSquareCompletion_npComplete :
    latinSquareCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L latinSquareCompletionDec

end MetaMathlibExt.Complexity.NPComplete.LatinSquareCompletion
