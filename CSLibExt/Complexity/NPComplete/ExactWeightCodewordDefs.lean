/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT-WEIGHT CODEWORD: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS7] DECODING OF
LINEAR CODES (comment: the variant asking for exactly `K` 1's is NP-complete,
even for fixed `y = (0, ..., 0)`);
E. R. Berlekamp, R. J. McEliece, and H. C. A. van Tilborg, "On the inherent
intractability of certain coding problems", IEEE Transactions on Information
Theory 24 (1978), 384-386, doi:10.1109/TIT.1978.1055873.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DecodingOfLinearCodesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactWeightCodeword

open Matrix

/-- Well-formedness of an instance: a well-formed DECODING OF LINEAR CODES instance (every
row of `A` has length `m = |y|`, and `0 < K`) whose vector `y` is all zero. -/
def WellFormed (i : DecodingOfLinearCodes.DecodingOfLinearCodesInstance) : Prop :=
  DecodingOfLinearCodes.WellFormed i ∧ ∀ b ∈ i.2.1, b = false

/-- Some `x ∈ (ZMod 2)ⁿ` with exactly `K` nonzero entries satisfies `x ᵥ* A = y`. -/
def ExactWeightCodewordFeasible (i : DecodingOfLinearCodes.DecodingOfLinearCodesInstance) :
    Prop :=
  ∃ x : Fin i.1.length → ZMod 2, hammingNorm x = i.2.2 ∧
    x ᵥ* DecodingOfLinearCodes.coeffMatrix i = DecodingOfLinearCodes.target i

open Classical in
/-- EXACT-WEIGHT CODEWORD as a decision problem over bitstrings. -/
noncomputable def exactWeightCodewordDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DecodingOfLinearCodes.DecodingOfLinearCodesInstance) x with
  | some i => decide (WellFormed i ∧ ExactWeightCodewordFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExactWeightCodeword
