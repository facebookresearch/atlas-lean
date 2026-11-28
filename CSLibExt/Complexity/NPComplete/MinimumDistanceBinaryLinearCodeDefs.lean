/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM DISTANCE OF A BINARY LINEAR CODE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS7] DECODING OF LINEAR CODES,
comment (the case `y = 0` with a nonzero codeword, listed there as open);
A. Vardy, "The intractability of computing the minimum distance of a code", IEEE
Transactions on Information Theory 43 (1997), 1757-1766, doi:10.1109/18.641542.
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.InformationTheory.Hamming
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DecodingOfLinearCodesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumDistanceBinaryLinearCode

open Matrix
open MetaMathlibExt.Complexity.NPComplete.DecodingOfLinearCodes
  (DecodingOfLinearCodesInstance coeffMatrix)

/-- An instance: the rows of `A` (`n` rows, each a list of `m` bits), the vector `y` (`m`
bits, required to be all zeros), and the bound `K`; this is the DECODING OF LINEAR CODES
instance type. -/
abbrev MinimumDistanceBinaryLinearCodeInstance := DecodingOfLinearCodesInstance

/-- Well-formedness of an instance: well-formed as a DECODING OF LINEAR CODES instance (every
row of `A` has length `m = |y|`, and `0 < K`), and `y` is the all-zero vector. -/
def WellFormed (i : MinimumDistanceBinaryLinearCodeInstance) : Prop :=
  DecodingOfLinearCodes.WellFormed i ∧ ∀ b ∈ i.2.1, b = false

/-- Some nonzero `x ∈ (ZMod 2)ⁿ` with at most `K` nonzero entries satisfies `x ᵥ* A = 0`. -/
def MinimumDistanceBinaryLinearCodeFeasible (i : MinimumDistanceBinaryLinearCodeInstance) :
    Prop :=
  ∃ x : Fin i.1.length → ZMod 2, x ≠ 0 ∧ hammingNorm x ≤ i.2.2 ∧ x ᵥ* coeffMatrix i = 0

open Classical in
/-- MINIMUM DISTANCE OF A BINARY LINEAR CODE as a decision problem over bitstrings. -/
noncomputable def minimumDistanceBinaryLinearCodeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumDistanceBinaryLinearCodeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumDistanceBinaryLinearCodeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumDistanceBinaryLinearCode
