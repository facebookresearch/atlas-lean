/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FINITE-FIELD SUBSET SUM: definitions

Source:
D. S. Johnson, "The NP-completeness column", ACM Transactions on Algorithms 1 (2005), 160-176,
doi:10.1145/1077464.1077476 (statement of FINITE-FIELD SUBSET SUM);
A. Vardy, "The intractability of computing the minimum distance of a code", IEEE Transactions on
Information Theory 43 (1997), 1757-1766, doi:10.1109/18.641542.
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.InformationTheory.Hamming
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DecodingOfLinearCodesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiniteFieldSubsetSum

open DecodingOfLinearCodes (DecodingOfLinearCodesInstance DecodingOfLinearCodesFeasible)

/-- Well-formedness of an instance `(α, β, K)`: `β` has `m > 0` coordinates, every `αᵢ` has
`m` coordinates (DECODING OF LINEAR CODES' well-formedness, which also gives `0 < K`), and the
elements `α₁, …, αₙ, β` are pairwise distinct. -/
def WellFormed (i : DecodingOfLinearCodesInstance) : Prop :=
  DecodingOfLinearCodes.WellFormed i ∧ 0 < i.2.1.length ∧ (i.1 ++ [i.2.1]).Nodup

open Classical in
/-- FINITE-FIELD SUBSET SUM as a decision problem over bitstrings. -/
noncomputable def finiteFieldSubsetSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DecodingOfLinearCodesInstance) x with
  | some i => decide (WellFormed i ∧ DecodingOfLinearCodesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FiniteFieldSubsetSum
