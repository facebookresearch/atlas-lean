/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEASIBLE BASIS EXTENSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP4] FEASIBLE BASIS EXTENSION;
K. G. Murty, "A fundamental problem in linear inequalities with applications to the travelling
salesman problem", Mathematical Programming 2 (1972), 296-308, doi:10.1007/BF01584550.
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeasibleBasisExtension

/-- An instance: `m`, `n`, the rows of `A`, the vector `a`, and the column indices `S`. -/
abbrev FeasibleBasisExtensionInstance :=
  ℕ × ℕ × List (List (ℕ × ℕ)) × List (ℕ × ℕ) × List ℕ

/-- The integer `p - q` encoded by `(p, q)`, as a rational number. -/
def intVal (z : ℕ × ℕ) : ℚ := (z.1 : ℚ) - z.2

/-- The matrix `A` over `ℚ`. -/
def matA (i : FeasibleBasisExtensionInstance) : Matrix (Fin i.1) (Fin i.2.1) ℚ :=
  Matrix.of fun r c => intVal ((i.2.2.1.getD r []).getD c (0, 0))

/-- The vector `a` over `ℚ`. -/
def vecA (i : FeasibleBasisExtensionInstance) : Fin i.1 → ℚ :=
  fun r => intVal (i.2.2.2.1.getD r (0, 0))

/-- Well-formedness of an instance: `A` has `m` rows of length `n`, `m < n`, `a` has length
`m`, and `S` is a set of fewer than `m` column indices. -/
def WellFormed (i : FeasibleBasisExtensionInstance) : Prop :=
  i.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.1, row.length = i.2.1) ∧ i.1 < i.2.1 ∧
    i.2.2.2.1.length = i.1 ∧ i.2.2.2.2.Nodup ∧ (∀ j ∈ i.2.2.2.2, j < i.2.1) ∧
    i.2.2.2.2.length < i.1

/-- A feasible basis containing `S`: `m` distinct columns, including every column of `S`, whose
submatrix `B` is nonsingular with `B⁻¹ a ≥ 0`. -/
def FeasibleBasisExtensionFeasible (i : FeasibleBasisExtensionInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1, Function.Injective σ ∧ (∀ j ∈ i.2.2.2.2, ∃ k, (σ k : ℕ) = j) ∧
    ((matA i).submatrix id σ).det ≠ 0 ∧
    ∀ k, 0 ≤ Matrix.mulVec ((matA i).submatrix id σ)⁻¹ (vecA i) k

open Classical in
/-- FEASIBLE BASIS EXTENSION as a decision problem over bitstrings. -/
noncomputable def feasibleBasisExtensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeasibleBasisExtensionInstance) x with
  | some i => decide (WellFormed i ∧ FeasibleBasisExtensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeasibleBasisExtension
