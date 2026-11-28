/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-DIVISIBILITY OF CYCLOTOMIC-TYPE PRODUCTS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN6] NON-DIVISIBILITY OF A PRODUCT
POLYNOMIAL, comment (p. 250);
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard", Proc. 17th
Annual Symposium on Foundations of Computer Science (1976), 264-267, doi:10.1109/SFCS.1976.29;
journal version SIAM Journal on Computing 7 (1978), 458-464, doi:10.1137/0207036.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfCyclotomicTypeProducts

/-- An instance: the sequences `⟨a₁, …, aₘ⟩` and `⟨b₁, …, bₙ⟩`. -/
abbrev NonDivisibilityOfCyclotomicTypeProductsInstance := List ℕ × List ℕ

/-- The product `∏ (z^a - 1)` over the entries `a` of a list, in `ℤ[z]`. -/
noncomputable def binomialProduct (l : List ℕ) : Polynomial ℤ :=
  (l.map fun a => Polynomial.X ^ a - 1).prod

/-- Well-formedness of an instance: every `aᵢ` and every `bⱼ` is positive. -/
def WellFormed (i : NonDivisibilityOfCyclotomicTypeProductsInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a) ∧ ∀ b ∈ i.2, 0 < b

/-- `∏ᵢ (z^{aᵢ} - 1)` does not divide `∏ⱼ (z^{bⱼ} - 1)` in `ℤ[z]`. -/
def NonDivisibilityOfCyclotomicTypeProductsFeasible
    (i : NonDivisibilityOfCyclotomicTypeProductsInstance) : Prop :=
  ¬ binomialProduct i.1 ∣ binomialProduct i.2

open Classical in
/-- NON-DIVISIBILITY OF CYCLOTOMIC-TYPE PRODUCTS as a decision problem over bitstrings. -/
noncomputable def nonDivisibilityOfCyclotomicTypeProductsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonDivisibilityOfCyclotomicTypeProductsInstance) x with
  | some i => decide (WellFormed i ∧ NonDivisibilityOfCyclotomicTypeProductsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfCyclotomicTypeProducts
