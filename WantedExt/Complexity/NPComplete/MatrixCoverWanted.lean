/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS13] MATRIX COVER
(credited there to Garey and Johnson, unpublished; transformation from MAX CUT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixCover

/-!
# MATRIX COVER is NP-complete

INSTANCE: an `n × n` matrix `A = (a i j)` with nonnegative integer entries, and an integer
`K`. QUESTION: is there a function `f : {1, ..., n} → {-1, +1}` such that
`∑_{1 ≤ i, j ≤ n} a i j * f i * f j ≤ K`?

The comparison is `≤`. With nonnegative entries every term satisfies
`a i j * f i * f j ≤ a i j`, so the constant function `f = +1` maximizes the sum and the
question with `≥` is decidable by adding up the entries. The `≤` question is the one the
transformation from MAX CUT proves NP-complete: for the adjacency matrix of a graph, the sum is
`2 * (|E| - 2 * c)` where `c` is the number of edges `f` cuts.

Indices are `0, ..., n - 1` here. Entries are natural numbers in binary; `K` is the integer
`K.1 - K.2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the side length `n`, the matrix `A` as a list of rows, and the bound `K` as a
pair `(K.1, K.2)` standing for the integer `K.1 - K.2`. -/
abbrev MatrixCoverInstance := ℕ × List (List ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: `A` has `n` rows of length `n`. -/
def WellFormed (i : MatrixCoverInstance) : Prop :=
  i.2.1.length = i.1 ∧ ∀ row ∈ i.2.1, row.length = i.1

/-- A sign function `f` (values `1` or `-1` on `0, ..., n - 1`) with
`∑_{r, c < n} A r c * f r * f c ≤ K`. -/
def MatrixCoverFeasible (i : MatrixCoverInstance) : Prop :=
  ∃ f : ℕ → ℤ, (∀ j < i.1, f j = 1 ∨ f j = -1) ∧
    ∑ r ∈ Finset.range i.1, ∑ c ∈ Finset.range i.1,
        ((i.2.1.getD r []).getD c 0 : ℤ) * f r * f c ≤ (i.2.2.1 : ℤ) - i.2.2.2

open Classical in
/-- MATRIX COVER as a decision problem over bitstrings. -/
noncomputable def matrixCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatrixCoverInstance) x with
  | some i => decide (WellFormed i ∧ MatrixCoverFeasible i)
  | none => false

/-- **MATRIX COVER is NP-complete.** Source: Garey and Johnson (1979), [MS13]. -/
public theorem_wanted matrixCover_npComplete :
    matrixCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L matrixCoverDec

end MetaMathlibExt.Complexity.NPComplete.MatrixCover
