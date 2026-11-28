/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST VECTOR PROBLEM is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestVector

/-!
# CLOSEST VECTOR PROBLEM is NP-complete

INSTANCE: a basis `(v₁, …, v_k)` for a lattice in `ℤᵏ`, a positive integer `K`, and a vector
`b ∈ ℤᵏ`.
QUESTION: does the lattice contain a vector `v = x₁v₁ + ⋯ + x_kv_k` with integral `xᵢ` such
that the Euclidean length `|v - b| ≤ K`?

This is van Emde Boas's NEAREST VECTOR problem, proved NP-complete in his Theorem 2, in the
Euclidean norm. A basis for a lattice in `ℤᵏ` is a list of `k` linearly independent vectors of
`ℤᵏ`; for `k` vectors of length `k` this is the nonvanishing of the `k × k` determinant. Since
`K ≥ 0` and all quantities are integers, `|v - b| ≤ K` is stated as
`∑ⱼ (vⱼ - bⱼ)² ≤ K²`. Each integer is encoded as a pair of naturals
`(positive part, negative part)` representing their difference, and numbers use the canonical
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CLOSEST VECTOR PROBLEM is NP-complete.** Source: van Emde Boas (1981), Theorem 2;
Micciancio (2001). -/
public theorem_wanted closestVector_npComplete :
    closestVectorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L closestVectorDec

end MetaMathlibExt.Complexity.NPComplete.ClosestVector
