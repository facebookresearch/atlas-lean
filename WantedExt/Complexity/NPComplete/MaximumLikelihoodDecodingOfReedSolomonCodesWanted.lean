/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM-LIKELIHOOD DECODING OF REED-SOLOMON CODES is NP-complete

Source:
V. Guruswami and A. Vardy, "Maximum-likelihood decoding of Reed-Solomon codes is NP-hard",
IEEE Transactions on Information Theory 51 (2005), 2249-2256, doi:10.1109/TIT.2005.850102
(preprint arXiv:cs/0405005).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Coding.ReedSolomon
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.RingTheory.AdjoinRoot
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodDecodingOfReedSolomonCodes

open Polynomial

/-!
# MAXIMUM-LIKELIHOOD DECODING OF REED-SOLOMON CODES is NP-complete

INSTANCE: an integer `m > 0`, a set `D = {x₁, x₂, …, xₙ}` consisting of `n` distinct elements of
`F_{2^m}`, an integer `k > 0`, a target vector `y ∈ F_{2^m}^n`, and an integer `w > 0`.
QUESTION: is there a codeword `c ∈ C_{2^m}(D, k)` such that `d(c, y) ≤ w`? Here the
Reed-Solomon code `C_{2^m}(D, k)` is the set of vectors `(f(x₁), …, f(xₙ))` for the polynomials
`f ∈ F_{2^m}[X]` with `deg f < k`, and `d` is the Hamming distance (Guruswami and Vardy,
Section 1, problem MLD-RS).

Field representation: Guruswami and Vardy represent the elements of `F_{2^m}` by `m`-bit
vectors; their reduction (Section 2, step B and Lemma 1) constructs the field from an irreducible
binary polynomial of degree `m` (by Shoup's deterministic algorithm) and writes each element in
the basis `1, α, …, α^{m-1}`, where `α` is a root of that polynomial. The instance therefore
also carries that polynomial: `f = f₀ + f₁ X + ⋯ + f_m X^m` over `ZMod 2`, listed by its bits
`f₀, …, f_m` with `f_m = 1` (`modulus`), so `m = deg f`. The field is
`AdjoinRoot f = (ZMod 2)[X] / (f)`, a field with `2^m` elements when `f` is irreducible, and an
`m`-bit vector `(v₀, …, v_{m-1})` stands for `v₀ + v₁ α + ⋯ + v_{m-1} α^{m-1}` with
`α = AdjoinRoot.root f` (`toField`). Distinct `m`-bit vectors are distinct elements, so the
points of `D` are distinct exactly when their bit vectors are. Irreducibility of a binary
polynomial is decidable in polynomial time, so this well-formedness condition does not affect
membership in NP; the reduction's polynomial is irreducible, so its instances are well formed.

The code is the repository's `Cslib.CodingTheory.ReedSolomon.code` (the evaluations at the
points of the polynomials of degree less than `k`), and the distance is Mathlib's
`hammingDist`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the bits `f₀, …, f_m` of the defining polynomial `f`, the points `x₁, …, xₙ`
of `D` and the target `y₁, …, yₙ` as `m`-bit vectors, the dimension `k`, and the bound `w`. -/
abbrev MaximumLikelihoodDecodingOfReedSolomonCodesInstance :=
  List Bool × List (List Bool) × ℕ × List (List Bool) × ℕ

/-- The bit `b` as an element of `ZMod 2`. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The defining polynomial `f₀ + f₁ X + ⋯ + f_m X^m` over `ZMod 2`. -/
noncomputable def modulus (i : MaximumLikelihoodDecodingOfReedSolomonCodesInstance) :
    (ZMod 2)[X] :=
  ∑ j ∈ Finset.range i.1.length, monomial j (bit (i.1.getD j false))

/-- The element `v₀ + v₁ α + ⋯ + v_{r-1} α^{r-1}` of `AdjoinRoot f`, where `α` is the root of
`f` and `v = (v₀, …, v_{r-1})`. -/
noncomputable def toField (i : MaximumLikelihoodDecodingOfReedSolomonCodesInstance)
    (v : List Bool) : AdjoinRoot (modulus i) :=
  ∑ j ∈ Finset.range v.length, AdjoinRoot.of (modulus i) (bit (v.getD j false)) *
    AdjoinRoot.root (modulus i) ^ j

/-- The evaluation points `x₁, …, xₙ`. -/
noncomputable def points (i : MaximumLikelihoodDecodingOfReedSolomonCodesInstance) :
    Fin i.2.1.length → AdjoinRoot (modulus i) :=
  fun j => toField i i.2.1[j]

/-- The target vector `y = (y₁, …, yₙ)`, indexed like the points. -/
noncomputable def target (i : MaximumLikelihoodDecodingOfReedSolomonCodesInstance) :
    Fin i.2.1.length → AdjoinRoot (modulus i) :=
  fun j => toField i (i.2.2.2.1.getD j [])

/-- Well-formedness of an instance: `f` has degree `m ≥ 1` with leading bit `1` and is
irreducible; the points are `m`-bit vectors, pairwise distinct; the target has one `m`-bit
vector per point; and `k > 0`, `w > 0`. -/
def WellFormed (i : MaximumLikelihoodDecodingOfReedSolomonCodesInstance) : Prop :=
  2 ≤ i.1.length ∧ i.1.getLast? = some true ∧ Irreducible (modulus i) ∧
    (∀ v ∈ i.2.1, v.length = i.1.length - 1) ∧ i.2.1.Nodup ∧
    i.2.2.2.1.length = i.2.1.length ∧ (∀ v ∈ i.2.2.2.1, v.length = i.1.length - 1) ∧
    0 < i.2.2.1 ∧ 0 < i.2.2.2.2

open Classical in
/-- Over the field `AdjoinRoot f` (with `f` irreducible), some codeword `c` of the Reed-Solomon
code of the points and dimension `k` is within Hamming distance `w` of the target. -/
def MaximumLikelihoodDecodingOfReedSolomonCodesFeasible
    (i : MaximumLikelihoodDecodingOfReedSolomonCodesInstance) : Prop :=
  ∃ hf : Irreducible (modulus i),
    letI : Fact (Irreducible (modulus i)) := ⟨hf⟩
    ∃ c ∈ Cslib.CodingTheory.ReedSolomon.code (points i) i.2.2.1,
      hammingDist c (target i) ≤ i.2.2.2.2

open Classical in
/-- MAXIMUM-LIKELIHOOD DECODING OF REED-SOLOMON CODES as a decision problem over bitstrings. -/
noncomputable def maximumLikelihoodDecodingOfReedSolomonCodesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumLikelihoodDecodingOfReedSolomonCodesInstance) x with
  | some i => decide (WellFormed i ∧ MaximumLikelihoodDecodingOfReedSolomonCodesFeasible i)
  | none => false

/-- **MAXIMUM-LIKELIHOOD DECODING OF REED-SOLOMON CODES is NP-complete.** Source: Guruswami and
Vardy (2005). -/
public theorem_wanted maximumLikelihoodDecodingOfReedSolomonCodes_npComplete :
    maximumLikelihoodDecodingOfReedSolomonCodesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLikelihoodDecodingOfReedSolomonCodesDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodDecodingOfReedSolomonCodes
