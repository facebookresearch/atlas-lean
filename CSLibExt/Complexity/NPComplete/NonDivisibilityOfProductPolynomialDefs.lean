/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-DIVISIBILITY OF A PRODUCT POLYNOMIAL: definitions

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

public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfProductPolynomial

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

end MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfProductPolynomial
