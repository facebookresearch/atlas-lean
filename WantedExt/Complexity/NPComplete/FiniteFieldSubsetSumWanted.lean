/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FINITE-FIELD SUBSET SUM is NP-complete

Source:
D. S. Johnson, "The NP-completeness column", ACM Transactions on Algorithms 1 (2005), 160-176,
doi:10.1145/1077464.1077476 (statement of FINITE-FIELD SUBSET SUM);
A. Vardy, "The intractability of computing the minimum distance of a code", IEEE Transactions on
Information Theory 43 (1997), 1757-1766, doi:10.1109/18.641542.
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

namespace MetaMathlibExt.Complexity.NPComplete.FiniteFieldSubsetSum

open DecodingOfLinearCodes (DecodingOfLinearCodesInstance DecodingOfLinearCodesFeasible)

/-!
# FINITE-FIELD SUBSET SUM is NP-complete

INSTANCE: an integer `m > 0`, distinct elements `α₁, …, αₙ, β` of `GF(2^m)`, and a positive
integer `K`. QUESTION: is there a subset of `K` or fewer elements of `{αᵢ : 1 ≤ i ≤ n}` which
sums to `β` in `GF(2^m)`?

Johnson (2005), on Vardy's proof that MINIMUM WEIGHT CODEWORD is NP-complete: "Starting from the
DECODING OF LINEAR CODES problem, Vardy first presents a transformation to FINITE-FIELD SUBSET
SUM: Given an integer `m > 0`, distinct elements `α₁, α₂, …, αₙ, β ∈ GF(2^m)`, and a positive
integer `K`, is there a subset of `K` or fewer elements of `{αᵢ : 1 ≤ i ≤ n}` which sums to `β`
in `GF(2^m)`?" Membership in NP: the subset is a certificate.

Only addition in `GF(2^m)` enters the question, and the additive group of `GF(2^m)` is the
vector space `GF(2)^m` (coordinates in any fixed basis over `GF(2)`, e.g. the polynomial basis).
So an element is given by its `m` coordinates, a list of `m` bits, and a sum of elements is the
coordinatewise sum mod 2. A subset of the `αᵢ` is a 0-1 vector `x` with at most `K` ones, and
its sum is `∑ᵢ xᵢ αᵢ`. This is DECODING OF LINEAR CODES (`DecodingOfLinearCodesWanted`, [MS7])
with the `αᵢ` as the rows of the matrix and `β` as the target, restricted to distinct rows and
a target that is not a row: its instance type and question `DecodingOfLinearCodesFeasible`
(`x ᵥ* A = y` over `ZMod 2` with Mathlib's `hammingNorm x ≤ K`) are reused unchanged, and
`WellFormed` adds `m > 0` and the distinctness of `α₁, …, αₙ, β`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **FINITE-FIELD SUBSET SUM is NP-complete.** Source: Vardy (1997), as recorded by Johnson
(2005). -/
public theorem_wanted finiteFieldSubsetSum_npComplete :
    finiteFieldSubsetSumDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L finiteFieldSubsetSumDec

end MetaMathlibExt.Complexity.NPComplete.FiniteFieldSubsetSum
