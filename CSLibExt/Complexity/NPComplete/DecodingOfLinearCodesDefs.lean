/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DECODING OF LINEAR CODES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS7] DECODING OF LINEAR CODES;
E. R. Berlekamp, R. J. McEliece, and H. C. A. van Tilborg, "On the inherent intractability of
certain coding problems", IEEE Transactions on Information Theory 24 (1978), 384-386,
doi:10.1109/TIT.1978.1055873 (COSET WEIGHTS).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.InformationTheory.Hamming

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DecodingOfLinearCodes

open Matrix

/-- An instance: the rows of `A` (`n` rows, each a list of `m` bits), the vector `y` (`m`
bits), and the bound `K`. -/
abbrev DecodingOfLinearCodesInstance := List (List Bool) × List Bool × ℕ

/-- The matrix `A` over `ZMod 2`, with rows indexed by `Fin n` and columns by `Fin m`. -/
def coeffMatrix (i : DecodingOfLinearCodesInstance) :
    Matrix (Fin i.1.length) (Fin i.2.1.length) (ZMod 2) :=
  fun r c => if (i.1.getD r []).getD c false then 1 else 0

/-- The vector `y` over `ZMod 2`. -/
def target (i : DecodingOfLinearCodesInstance) : Fin i.2.1.length → ZMod 2 :=
  fun c => if i.2.1.getD c false then 1 else 0

/-- Well-formedness of an instance: every row of `A` has length `m = |y|`, and `0 < K`. -/
def WellFormed (i : DecodingOfLinearCodesInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.2.1.length) ∧ 0 < i.2.2

/-- Some `x ∈ (ZMod 2)ⁿ` with at most `K` nonzero entries satisfies `x ᵥ* A = y`. -/
def DecodingOfLinearCodesFeasible (i : DecodingOfLinearCodesInstance) : Prop :=
  ∃ x : Fin i.1.length → ZMod 2, hammingNorm x ≤ i.2.2 ∧ x ᵥ* coeffMatrix i = target i

open Classical in
/-- DECODING OF LINEAR CODES as a decision problem over bitstrings. -/
noncomputable def decodingOfLinearCodesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DecodingOfLinearCodesInstance) x with
  | some i => decide (WellFormed i ∧ DecodingOfLinearCodesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DecodingOfLinearCodes
