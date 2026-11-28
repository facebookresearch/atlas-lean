/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION PATTERN: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP9] INTERSECTION PATTERN (reference:
[Chvátal, 1978]; transformation from GRAPH 3-COLORABILITY);
V. Chvátal, "Recognizing intersection patterns", Annals of Discrete Mathematics 8 (1980),
249-251, doi:10.1016/S0167-5060(08)70883-5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionPattern

/-- An instance: the rows of the matrix `A`. -/
abbrev IntersectionPatternInstance := List (List ℕ)

/-- Well-formedness of an instance: `A` is square, every row having as many entries as there are
rows. -/
def WellFormed (A : IntersectionPatternInstance) : Prop :=
  ∀ row ∈ A, row.length = A.length

/-- Some sets `C₀, ..., C_{n-1}` satisfy `|Cᵢ ∩ Cⱼ| = a_ij` for all `i, j`. -/
def IntersectionPatternFeasible (A : IntersectionPatternInstance) : Prop :=
  ∃ C : Fin A.length → Finset ℕ, ∀ i j : Fin A.length,
    (C i ∩ C j).card = (A.getD i []).getD j 0

open Classical in
/-- INTERSECTION PATTERN as a decision problem over bitstrings. -/
noncomputable def intersectionPatternDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntersectionPatternInstance) x with
  | some A => decide (WellFormed A ∧ IntersectionPatternFeasible A)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntersectionPattern
