/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM-LIKELIHOOD DECODING OF REED-SOLOMON CODES: definitions

Source:
V. Guruswami and A. Vardy, "Maximum-likelihood decoding of Reed-Solomon codes is NP-hard",
IEEE Transactions on Information Theory 51 (2005), 2249-2256, doi:10.1109/TIT.2005.850102
(preprint arXiv:cs/0405005).
-/
module

public import CSLibExt.Coding.ReedSolomon
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.RingTheory.AdjoinRoot
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodDecodingOfReedSolomonCodes

open Polynomial

/-- An instance: the bits `f₀, …, f_m` of the defining polynomial `f`, the points `x₁, …, xₙ`
of `D` and the target `y₁, …, yₙ` as `m`-bit vectors, the degree bound `k` (the code's dimension
when the points are distinct and `k ≤ n`, as `WellFormed` requires), and the bound `w`. -/
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
vector per point; `0 < k ≤ n` (the code has length `n` and dimension `k`); and `w > 0`. -/
def WellFormed (i : MaximumLikelihoodDecodingOfReedSolomonCodesInstance) : Prop :=
  2 ≤ i.1.length ∧ i.1.getLast? = some true ∧ Irreducible (modulus i) ∧
    (∀ v ∈ i.2.1, v.length = i.1.length - 1) ∧ i.2.1.Nodup ∧
    i.2.2.2.1.length = i.2.1.length ∧ (∀ v ∈ i.2.2.2.1, v.length = i.1.length - 1) ∧
    0 < i.2.2.1 ∧ i.2.2.1 ≤ i.2.1.length ∧ 0 < i.2.2.2.2

open Classical in
/-- Over the field `AdjoinRoot f` (with `f` irreducible), some codeword `c` of the Reed-Solomon
code of the points with degree bound `k` (evaluations of polynomials of degree less than `k`) is
within Hamming distance `w` of the target. Distinct points and `k ≤ n` are not checked here;
under `WellFormed` the code has dimension `k`. -/
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

end MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodDecodingOfReedSolomonCodes
