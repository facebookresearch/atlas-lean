/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM DISTANCE OF A BINARY LINEAR CODE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS7] DECODING OF LINEAR CODES,
comment (the case `y = 0` with a nonzero codeword, listed there as open);
A. Vardy, "The intractability of computing the minimum distance of a code", IEEE
Transactions on Information Theory 43 (1997), 1757-1766, doi:10.1109/18.641542.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.InformationTheory.Hamming
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DecodingOfLinearCodesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumDistanceBinaryLinearCode

open Matrix
open MetaMathlibExt.Complexity.NPComplete.DecodingOfLinearCodes
  (DecodingOfLinearCodesInstance coeffMatrix)

/-!
# MINIMUM DISTANCE OF A BINARY LINEAR CODE is NP-complete

INSTANCE: an `n × m` matrix `A = (aᵢⱼ)` of 0's and 1's and a positive integer `K`.
QUESTION: is there a nonzero 0-1 vector `x = (x₁, ..., xₙ)` with no more than `K` 1's such
that, for `1 ≤ j ≤ m`, `∑ᵢ xᵢ aᵢⱼ ≡ 0 (mod 2)`, that is, a nonzero codeword of Hamming weight
at most `K` of the binary linear code with parity-check matrix `Aᵀ`?

This is DECODING OF LINEAR CODES
(`WantedExt.Complexity.NPComplete.DecodingOfLinearCodesWanted`) with the vector `y` fixed to
the all-zero vector and `x` required to be nonzero, the case Garey and Johnson list as open;
Vardy (1997) proved it NP-complete. The instance and the matrix `A` over `ZMod 2` are those of
the DECODING OF LINEAR CODES module, reused here, with `y` required to be all zeros; the
congruences are the vector equation `x ᵥ* A = 0` (Mathlib's `Matrix.vecMul`), and the number of
1's of `x` is Mathlib's `hammingNorm x`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MINIMUM DISTANCE OF A BINARY LINEAR CODE is NP-complete.** Source: Garey and Johnson
(1979), [MS7], comment; Vardy (1997). -/
public theorem_wanted minimumDistanceBinaryLinearCode_npComplete :
    minimumDistanceBinaryLinearCodeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumDistanceBinaryLinearCodeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumDistanceBinaryLinearCode
