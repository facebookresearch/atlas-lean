/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import CSLibExt.Complexity.NPComplete.QuadraticProgrammingDefs

/-!
# SPARSE APPROXIMATION: definitions

INSTANCE: a matrix `A ∈ ℚ^{m × n}`, a vector `b ∈ ℚ^m`, a rational `ε > 0`, and a nonnegative
integer `k`.
QUESTION: is there a vector `x ∈ ℝ^n` with at most `k` nonzero entries and `‖Ax - b‖₂ ≤ ε`?

Natarajan considers the problem "given a matrix A in R^{m×n}, a vector b in R^m, and ε > 0,
compute a vector x satisfying ‖Ax - b‖₂ ≤ ε if such exists, such that x has the fewest number of
non-zero entries over all such vectors" and shows that it is NP-hard; this is its decision
version with the bound `k` on the number of nonzero entries. It is in NP: a support of size at
most `k` is a certificate, and for a fixed support the least residual is a least-squares problem
solvable exactly over `ℚ`.

The input numbers are rationals, given as `((a, b), d)` with value `(a - b) / d` and `0 < d`
(`QuadraticProgramming.RatCode`, `QuadraticProgramming.ratVal`, reused from
`QuadraticProgrammingDefs`);
`ε` must be positive. The matrix is a list of `m` rows of `n` entries and `b` a list of `m`
entries. `x` ranges over real vectors `Fin n → ℝ`, the number of nonzero entries is the size of
its support, and `‖·‖₂` is the Euclidean norm `√(∑ᵢ (∑ⱼ Aᵢⱼ xⱼ - bᵢ)²)`. All numbers use the
canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
B. K. Natarajan, "Sparse approximate solutions to linear systems", SIAM Journal on Computing 24
(1995), 227-234, doi:10.1137/S0097539792240406.
-/

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
