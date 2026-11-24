/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPARSE MATRIX COMPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR13] SPARSE MATRIX COMPRESSION (reference:
[Even, Lichtenstein, and Shiloach, 1977]; transformation from GRAPH 3-COLORABILITY);
S. Even, D. I. Lichtenstein and Y. Shiloach, "Remarks on Ziegler's method for matrix
compression", unpublished manuscript (1977);
V. Jugé, D. Köppl, V. Limouzy, A. Marino, J. Olblich, G. Punzi and T. Uno, "Revisiting the
sparse matrix compression problem", arXiv:2602.15314 (2026), Section 1 (records the result).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompression

/-!
# SPARSE MATRIX COMPRESSION is NP-complete

INSTANCE: an `m × n` matrix `A` with entries `a_ij ∈ {0, 1}`, `1 ≤ i ≤ m`, `1 ≤ j ≤ n`, and a
positive integer `K ≤ mn`.
QUESTION: is there a sequence `(b₁, b₂, ..., b_{n+K})` of integers `bᵢ`, each satisfying
`0 ≤ bᵢ ≤ m`, and a function `s : {1, 2, ..., m} → {1, 2, ..., K}` such that, for `1 ≤ i ≤ m`
and `1 ≤ j ≤ n`, the entry `a_ij = 1` if and only if `b_{s(i)+j-1} = i`?

The matrix is the list of its `m` rows, each a list of `n` truth values (`true` for `1`). Rows,
columns, shifts and positions of `b` are indexed from `0`: row `r` is row `i = r + 1`, column `c`
is column `j = c + 1`, the shift `s r ∈ {0, …, K - 1}` is `s(i) - 1`, and `b` is a list of
length `n + K` whose entry at position `t` is `b_{t+1}`. Then `b_{s(i)+j-1}` is the entry of `b`
at position `s r + c`, and the condition `b_{s(i)+j-1} = i` reads `b[s r + c] = r + 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of columns, the rows of `A` (each a list of `n` entries, `true`
for `1`), and the bound `K`. -/
abbrev SparseMatrixCompressionInstance := ℕ × List (List Bool) × ℕ

/-- Well-formedness of an instance: every row has exactly `n` entries, and `0 < K ≤ mn`. -/
def WellFormed (i : SparseMatrixCompressionInstance) : Prop :=
  (∀ row ∈ i.2.1, row.length = i.1) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length * i.1

/-- A sequence `b` of `n + K` integers in `{0, …, m}` and shifts `s` such that `a_rc = 1` exactly
when `b` holds `r + 1` at position `s r + c`. -/
def SparseMatrixCompressionFeasible (i : SparseMatrixCompressionInstance) : Prop :=
  ∃ b : List ℕ, b.length = i.1 + i.2.2 ∧ (∀ x ∈ b, x ≤ i.2.1.length) ∧
    ∃ s : Fin i.2.1.length → Fin i.2.2, ∀ r : Fin i.2.1.length, ∀ c : Fin i.1,
      ((i.2.1.getD r []).getD c false = true ↔ b.getD (s r + c) 0 = r + 1)

open Classical in
/-- SPARSE MATRIX COMPRESSION as a decision problem over bitstrings. -/
noncomputable def sparseMatrixCompressionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SparseMatrixCompressionInstance) x with
  | some i => decide (WellFormed i ∧ SparseMatrixCompressionFeasible i)
  | none => false

/-- **SPARSE MATRIX COMPRESSION is NP-complete.** Source: Garey and Johnson (1979), [SR13];
Even, Lichtenstein and Shiloach (1977). -/
public theorem_wanted sparseMatrixCompression_npComplete :
    sparseMatrixCompressionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sparseMatrixCompressionDec

end MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompression
