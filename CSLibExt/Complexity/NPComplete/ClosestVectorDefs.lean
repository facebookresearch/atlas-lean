/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST VECTOR PROBLEM: definitions

Source:
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Mathematisch Instituut, University of Amsterdam (1981),
p. 2, problem NEAREST VECTOR and Theorem 2;
D. Micciancio, "The shortest vector in a lattice is hard to approximate to within some
constant", SIAM J. Comput. 30 (2001), 2008-2035, doi:10.1137/S0097539700373039, Sections 1-2
(the closest vector problem "was proved NP-hard to solve exactly by van Emde Boas", who calls it
"Nearest Vector").
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestVector

/-- An instance: the basis vectors `v₁, …, v_k` (each a list of integer coordinates, encoded as
`(positive part, negative part)` pairs), the target `b` (encoded the same way), and the bound
`K`. -/
abbrev ClosestVectorInstance := List (List (ℕ × ℕ)) × List (ℕ × ℕ) × ℕ

/-- The dimension `k`: the number of basis vectors. -/
def dim (i : ClosestVectorInstance) : ℕ := i.1.length

/-- The integer encoded by a `(positive part, negative part)` pair. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- The `k × k` integer matrix whose rows are the basis vectors. -/
def basisMatrix (i : ClosestVectorInstance) : Matrix (Fin (dim i)) (Fin (dim i)) ℤ :=
  Matrix.of fun a j => intOf ((i.1.getD a []).getD j (0, 0))

/-- The target vector `b`. -/
def target (i : ClosestVectorInstance) : Fin (dim i) → ℤ :=
  fun j => intOf (i.2.1.getD j (0, 0))

/-- Well-formedness of an instance: there are `k` basis vectors, each with `k` coordinates, they
are linearly independent (the determinant is nonzero), the target has `k` coordinates, and `K`
is positive. -/
def WellFormed (i : ClosestVectorInstance) : Prop :=
  (∀ row ∈ i.1, row.length = dim i) ∧ (basisMatrix i).det ≠ 0 ∧ i.2.1.length = dim i ∧
    0 < i.2.2

/-- Some integer coefficient vector `x` gives a lattice vector
`v = x₁v₁ + ⋯ + x_kv_k = Matrix.vecMul x (basisMatrix i)` within Euclidean distance `K` of `b`. -/
def ClosestVectorFeasible (i : ClosestVectorInstance) : Prop :=
  ∃ x : Fin (dim i) → ℤ,
    ∑ j, (Matrix.vecMul x (basisMatrix i) j - target i j) ^ 2 ≤ (i.2.2 : ℤ) ^ 2

open Classical in
/-- CLOSEST VECTOR PROBLEM as a decision problem over bitstrings. -/
noncomputable def closestVectorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClosestVectorInstance) x with
  | some i => decide (WellFormed i ∧ ClosestVectorFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ClosestVector
