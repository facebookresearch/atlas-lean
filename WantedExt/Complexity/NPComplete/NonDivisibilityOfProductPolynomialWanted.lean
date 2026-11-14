/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-DIVISIBILITY OF A PRODUCT POLYNOMIAL is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN6] NON-DIVISIBILITY OF A PRODUCT
POLYNOMIAL;
D. A. Plaisted, "Sparse complex polynomials and polynomial reducibility", Journal of Computer
and System Sciences 14 (1977), 210-221, doi:10.1016/S0022-0000(77)80013-5;
D. A. Plaisted, "New NP-hard and NP-complete polynomial and integer divisibility problems",
Proc. 18th Annual Symposium on Foundations of Computer Science (1977), 241-253,
doi:10.1109/SFCS.1977.17; journal version Theoretical Computer Science 31 (1984), 125-138,
doi:10.1016/0304-3975(84)90130-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfProductPolynomial

/-!
# NON-DIVISIBILITY OF A PRODUCT POLYNOMIAL is NP-complete

Given sequences `Aᵢ = ⟨(aᵢ[1], bᵢ[1]), …, (aᵢ[kᵢ], bᵢ[kᵢ])⟩`, `1 ≤ i ≤ m`, of pairs of
integers with every exponent `bᵢ[j] ≥ 0`, and a positive integer `N`, is the product
`∏ᵢ (∑ⱼ aᵢ[j] z^{bᵢ[j]})` *not* divisible by `z^N - 1`?

Each `Aᵢ` is the sparse representation of the integer polynomial
`pᵢ(z) = ∑ⱼ aᵢ[j] z^{bᵢ[j]}`; divisibility is taken in `ℤ[z]` (`Polynomial ℤ`). Because
`z^N - 1` is monic, this is the same as divisibility in `ℚ[z]` or `ℂ[z]`. A coefficient
`aᵢ[j]` is encoded as a pair of naturals `(positive part, negative part)` whose difference it
is, as in `ZeroOneILPWanted`; an exponent `bᵢ[j] ≥ 0` is a natural number. Coefficients,
exponents and `N` use the canonical binary encoding, so degrees can be exponential in the input
size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the sequences `A₁, …, Aₘ`, each a list of
`((positive part, negative part) of aᵢ[j], bᵢ[j])`, and `N`. -/
abbrev NonDivisibilityOfProductPolynomialInstance := List (List ((ℕ × ℕ) × ℕ)) × ℕ

/-- The integer polynomial `∑ⱼ aⱼ z^{bⱼ}` of a sparse representation
`⟨((a⁺ⱼ, a⁻ⱼ), bⱼ)⟩ⱼ`, with `aⱼ = a⁺ⱼ - a⁻ⱼ`. -/
noncomputable def sparsePoly (A : List ((ℕ × ℕ) × ℕ)) : Polynomial ℤ :=
  (A.map fun t => Polynomial.C ((t.1.1 : ℤ) - t.1.2) * Polynomial.X ^ t.2).sum

/-- Well-formedness of an instance: `N` is positive. -/
def WellFormed (i : NonDivisibilityOfProductPolynomialInstance) : Prop :=
  0 < i.2

/-- The product `∏ᵢ pᵢ(z)` is not divisible by `z^N - 1` in `ℤ[z]`. -/
def NonDivisibilityOfProductPolynomialFeasible
    (i : NonDivisibilityOfProductPolynomialInstance) : Prop :=
  ¬ ((Polynomial.X : Polynomial ℤ) ^ i.2 - 1 ∣ (i.1.map sparsePoly).prod)

open Classical in
/-- NON-DIVISIBILITY OF A PRODUCT POLYNOMIAL as a decision problem over bitstrings. -/
noncomputable def nonDivisibilityOfProductPolynomialDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonDivisibilityOfProductPolynomialInstance) x with
  | some i => decide (WellFormed i ∧ NonDivisibilityOfProductPolynomialFeasible i)
  | none => false

/-- **NON-DIVISIBILITY OF A PRODUCT POLYNOMIAL is NP-complete.** Source: Garey and Johnson
(1979), [AN6]; Plaisted (1977, 1984). -/
public theorem_wanted nonDivisibilityOfProductPolynomial_npComplete :
    nonDivisibilityOfProductPolynomialDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonDivisibilityOfProductPolynomialDec

end MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfProductPolynomial
