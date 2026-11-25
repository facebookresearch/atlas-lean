/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST VECTOR PROBLEM IN THE MAX NORM is NP-complete

Source:
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Mathematisch Instituut, University of Amsterdam (1981),
p. 2, problem CLOSEST VECTOR and Theorem 2;
D. Micciancio, "The shortest vector in a lattice is hard to approximate to within some
constant", SIAM J. Comput. 30 (2001), 2008-2035, doi:10.1137/S0097539700373039, Section 1 and
footnote 1 (van Emde Boas's "Closest Vector" is the shortest vector problem in the `ℓ∞` norm).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestVectorMaxNorm

/-!
# SHORTEST VECTOR PROBLEM IN THE MAX NORM is NP-complete

INSTANCE: a basis `(v₁, …, v_k)` for a lattice in `ℤᵏ`, and a positive integer `K`.
QUESTION: does the lattice contain a vector `v = x₁v₁ + ⋯ + x_kv_k` with integers
`(x₁, …, x_k) ≠ (0, …, 0)` and all coordinates of `v` bounded by `K` in absolute value, that is,
`‖v‖_∞ ≤ K`?

This is van Emde Boas's CLOSEST VECTOR problem (his name; today it is the shortest vector problem
in the max norm), proved NP-complete in his Theorem 2. A basis for a lattice in `ℤᵏ` is a list
of `k` linearly independent vectors of `ℤᵏ`; for `k` vectors of length `k` this is the
nonvanishing of the `k × k` determinant. Each integer is encoded as a pair of naturals
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

/-- **SHORTEST VECTOR PROBLEM IN THE MAX NORM is NP-complete.** Source: van Emde Boas (1981),
Theorem 2; Micciancio (2001). -/
public theorem_wanted shortestVectorMaxNorm_npComplete :
    shortestVectorMaxNormDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestVectorMaxNormDec

end MetaMathlibExt.Complexity.NPComplete.ShortestVectorMaxNorm
