/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX DOMINATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS12] MATRIX DOMINATION;
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on
Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixDomination

/-- An instance: the side length `n`, the matrix `M` as a list of rows (`true` for `1`), and
the bound `K`. -/
abbrev MatrixDominationInstance := ℕ × List (List Bool) × ℕ

/-- Well-formedness of an instance: `M` has `n` rows of length `n`, and `0 < K`. -/
def WellFormed (i : MatrixDominationInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧ 0 < i.2.2

/-- Entry `(r, c)` of `M` is `1`; positions outside the matrix are not entries. -/
def Entry (i : MatrixDominationInstance) (r c : ℕ) : Prop :=
  (i.2.1.getD r []).getD c false = true

/-- A set `C` of at most `K` non-zero entries such that every non-zero entry shares its row or
its column with an entry of `C`. -/
def MatrixDominationFeasible (i : MatrixDominationInstance) : Prop :=
  ∃ C : Finset (ℕ × ℕ), C.card ≤ i.2.2 ∧ (∀ p ∈ C, Entry i p.1 p.2) ∧
    ∀ r c, Entry i r c → ∃ p ∈ C, p.1 = r ∨ p.2 = c

open Classical in
/-- MATRIX DOMINATION as a decision problem over bitstrings. -/
noncomputable def matrixDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatrixDominationInstance) x with
  | some i => decide (WellFormed i ∧ MatrixDominationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MatrixDomination
