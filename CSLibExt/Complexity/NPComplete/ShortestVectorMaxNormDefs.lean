/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST VECTOR PROBLEM IN THE MAX NORM: definitions

Source:
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Mathematisch Instituut, University of Amsterdam (1981),
p. 2, problem CLOSEST VECTOR and Theorem 2;
D. Micciancio, "The shortest vector in a lattice is hard to approximate to within some
constant", SIAM J. Comput. 30 (2001), 2008-2035, doi:10.1137/S0097539700373039, Section 1 and
footnote 1 (van Emde Boas's "Closest Vector" is the shortest vector problem in the `ℓ∞` norm).
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestVectorMaxNorm

/-- An instance: the basis vectors `v₁, …, v_k` (each a list of integer coordinates, encoded as
`(positive part, negative part)` pairs) and the bound `K`. -/
abbrev ShortestVectorMaxNormInstance := List (List (ℕ × ℕ)) × ℕ

/-- The dimension `k`: the number of basis vectors. -/
def dim (i : ShortestVectorMaxNormInstance) : ℕ := i.1.length

/-- Coordinate `j` of basis vector `vᵢ`, as an integer. -/
def entry (i : ShortestVectorMaxNormInstance) (a j : ℕ) : ℤ :=
  (((i.1.getD a []).getD j (0, 0)).1 : ℤ) - (((i.1.getD a []).getD j (0, 0)).2 : ℤ)

/-- The `k × k` integer matrix whose rows are the basis vectors. -/
def basisMatrix (i : ShortestVectorMaxNormInstance) : Matrix (Fin (dim i)) (Fin (dim i)) ℤ :=
  Matrix.of fun a j => entry i a j

/-- Well-formedness of an instance: there are `k` basis vectors, each with `k` coordinates, they
are linearly independent (the determinant is nonzero), and `K` is positive. -/
def WellFormed (i : ShortestVectorMaxNormInstance) : Prop :=
  (∀ row ∈ i.1, row.length = dim i) ∧ (basisMatrix i).det ≠ 0 ∧ 0 < i.2

/-- Some nonzero integer coefficient vector `x` gives a lattice vector
`v = x₁v₁ + ⋯ + x_kv_k = Matrix.vecMul x (basisMatrix i)` with every coordinate of absolute
value at most `K`. -/
def ShortestVectorMaxNormFeasible (i : ShortestVectorMaxNormInstance) : Prop :=
  ∃ x : Fin (dim i) → ℤ, x ≠ 0 ∧ ∀ j, |Matrix.vecMul x (basisMatrix i) j| ≤ (i.2 : ℤ)

open Classical in
/-- SHORTEST VECTOR PROBLEM IN THE MAX NORM as a decision problem over bitstrings. -/
noncomputable def shortestVectorMaxNormDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestVectorMaxNormInstance) x with
  | some i => decide (WellFormed i ∧ ShortestVectorMaxNormFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortestVectorMaxNorm
