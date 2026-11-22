/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-DIVISIBILITY OF CYCLOTOMIC-TYPE PRODUCTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN6] NON-DIVISIBILITY OF A PRODUCT
POLYNOMIAL, comment (p. 250);
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard", Proc. 17th
Annual Symposium on Foundations of Computer Science (1976), 264-267, doi:10.1109/SFCS.1976.29;
journal version SIAM Journal on Computing 7 (1978), 458-464, doi:10.1137/0207036.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfCyclotomicTypeProducts

/-!
# NON-DIVISIBILITY OF CYCLOTOMIC-TYPE PRODUCTS is NP-complete

Given two sequences `⟨a₁, …, aₘ⟩` and `⟨b₁, …, bₙ⟩` of positive integers, does
`∏ᵢ (z^{aᵢ} - 1)` *not* divide `∏ⱼ (z^{bⱼ} - 1)`?

This is the related problem recorded in the comment of Garey and Johnson's [AN6]. Divisibility
is taken in `ℤ[z]` (`Polynomial ℤ`); every factor `z^a - 1` is monic, so this is the same as
divisibility in `ℚ[z]` or `ℂ[z]`. An empty sequence has the empty product `1`. The integers
`aᵢ` and `bⱼ` use the canonical binary encoding, so degrees can be exponential in the input
size.

Membership in NP despite the large degrees: `z^a - 1 = ∏_{d ∣ a} Φ_d(z)` with distinct
irreducible cyclotomic polynomials `Φ_d`, so the first product fails to divide the second
exactly when some `d` divides more of the `aᵢ` than of the `bⱼ`; such a `d` is at most
`max aᵢ`, has a binary certificate, and the two counts take polynomially many divisibility
tests.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **NON-DIVISIBILITY OF CYCLOTOMIC-TYPE PRODUCTS is NP-complete.** Source: Garey and
Johnson (1979), [AN6], comment; Plaisted (1976). -/
public theorem_wanted nonDivisibilityOfCyclotomicTypeProducts_npComplete :
    nonDivisibilityOfCyclotomicTypeProductsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonDivisibilityOfCyclotomicTypeProductsDec

end MetaMathlibExt.Complexity.NPComplete.NonDivisibilityOfCyclotomicTypeProducts
