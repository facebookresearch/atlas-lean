/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPARSE MATRIX COMPRESSION: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompression

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

end MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompression
