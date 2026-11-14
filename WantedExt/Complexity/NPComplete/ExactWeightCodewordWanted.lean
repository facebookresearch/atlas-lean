/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT-WEIGHT CODEWORD is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DecodingOfLinearCodesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactWeightCodeword

open Matrix

/-!
# EXACT-WEIGHT CODEWORD is NP-complete

INSTANCE: an `n × m` matrix `A = (aᵢⱼ)` of 0's and 1's, the all-zero vector
`y = (0, ..., 0)` of length `m`, and a positive integer `K`. QUESTION: is there a 0-1 vector
`x = (x₁, ..., xₙ)` with exactly `K` 1's such that, for `1 ≤ j ≤ m`,
`∑ᵢ xᵢ aᵢⱼ ≡ yⱼ (mod 2)`, i.e. a nonzero "codeword" `x` of Hamming weight exactly `K` with
`x A ≡ 0 (mod 2)`?

This is DECODING OF LINEAR CODES (`MetaMathlibExt.Complexity.NPComplete.DecodingOfLinearCodes`)
with "no more than `K`" replaced by "exactly `K`" and the vector `y` fixed to zero. The
instance type, the matrix `A` and the vector `y` over `ZMod 2` are reused from that module;
`y` is still part of the instance (it carries `m`) and must be all zero. The number of 1's of
`x` is Mathlib's `hammingNorm x`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **EXACT-WEIGHT CODEWORD is NP-complete.** Source: Garey and Johnson (1979), [MS7];
Berlekamp, McEliece, and van Tilborg (1978). -/
public theorem_wanted exactWeightCodeword_npComplete :
    exactWeightCodewordDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L exactWeightCodewordDec

end MetaMathlibExt.Complexity.NPComplete.ExactWeightCodeword
