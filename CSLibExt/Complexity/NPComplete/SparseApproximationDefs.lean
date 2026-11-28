/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPARSE APPROXIMATION: definitions

Source:
B. K. Natarajan, "Sparse approximate solutions to linear systems", SIAM Journal on Computing 24
(1995), 227-234, doi:10.1137/S0097539792240406.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import CSLibExt.Complexity.NPComplete.QuadraticProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SparseApproximation

open QuadraticProgramming (RatCode ratVal)

/-- An instance: the number of columns `n`, the rows of `A`, the vector `b`, `ε`, and `k`. -/
abbrev SparseApproximationInstance := ℕ × List (List RatCode) × List RatCode × RatCode × ℕ

/-- The entry `A_{rc}` of the matrix. -/
def entry (i : SparseApproximationInstance) (r c : ℕ) : ℚ :=
  ratVal ((i.2.1.getD r []).getD c ((0, 0), 1))

/-- The entry `b_r` of the vector. -/
def rhs (i : SparseApproximationInstance) (r : ℕ) : ℚ :=
  ratVal (i.2.2.1.getD r ((0, 0), 1))

/-- Well-formedness of an instance: `A` has one row of `n` entries per entry of `b`, every
denominator is positive, and `ε > 0`. -/
def WellFormed (i : SparseApproximationInstance) : Prop :=
  i.2.1.length = i.2.2.1.length ∧ (∀ row ∈ i.2.1, row.length = i.1 ∧ ∀ q ∈ row, 0 < q.2) ∧
    (∀ q ∈ i.2.2.1, 0 < q.2) ∧ 0 < i.2.2.2.1.2 ∧ 0 < ratVal i.2.2.2.1

/-- Some real vector `x` with at most `k` nonzero entries has `‖Ax - b‖₂ ≤ ε`. -/
def SparseApproximationFeasible (i : SparseApproximationInstance) : Prop :=
  ∃ x : Fin i.1 → ℝ, (Finset.univ.filter fun c => x c ≠ 0).card ≤ i.2.2.2.2 ∧
    Real.sqrt (∑ r : Fin i.2.2.1.length,
      ((∑ c : Fin i.1, (entry i r c : ℝ) * x c) - rhs i r) ^ 2) ≤ ratVal i.2.2.2.1

open Classical in
/-- SPARSE APPROXIMATION as a decision problem over bitstrings. -/
noncomputable def sparseApproximationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SparseApproximationInstance) x with
  | some i => decide (WellFormed i ∧ SparseApproximationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SparseApproximation
