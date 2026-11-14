/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COSINE PRODUCT INTEGRATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN14] COSINE PRODUCT
INTEGRATION;
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard",
Proc. 17th Annual Symposium on Foundations of Computer Science (1976), 264-267,
doi:10.1109/SFCS.1976.29; journal version SIAM Journal on Computing 7 (1978),
458-464, doi:10.1137/0207036.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CosineProductIntegration

/-!
# COSINE PRODUCT INTEGRATION is NP-complete

INSTANCE: a sequence `(a₁, ..., aₙ)` of integers. QUESTION: is
`∫₀^{2π} ∏ᵢ cos(aᵢ θ) dθ ≠ 0`?

The integral equals `2π · 2⁻ⁿ` times the number of sign vectors `ε ∈ {±1}ⁿ` with
`∑ εᵢ aᵢ = 0`, so it is nonzero exactly when the `aᵢ` split into two parts of equal sum.
Garey and Johnson print the question with `= 0`; read literally, that is the complement of
this problem (a coNP question). The NP-complete question, which Plaisted's reduction from
PARTITION decides, is whether the integral is nonzero.

Each integer is encoded as a pair of naturals `(positive part, negative part)` representing
their difference, with one of the two parts zero, so every integer has exactly one encoding.
The numbers use the canonical binary encoding; the problem is NP-complete in the weak sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the sequence `(a₁, ..., aₙ)`, each integer as a pair (positive part,
negative part). -/
abbrev CosineProductIntegrationInstance := List (ℕ × ℕ)

/-- The integer an encoded pair represents. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- Well-formedness of an instance: every pair is in canonical form (one part is zero). -/
def WellFormed (i : CosineProductIntegrationInstance) : Prop :=
  ∀ p ∈ i, p.1 = 0 ∨ p.2 = 0

/-- The integral `∫₀^{2π} ∏ᵢ cos(aᵢ θ) dθ` is nonzero. -/
def CosineProductIntegrationFeasible (i : CosineProductIntegrationInstance) : Prop :=
  (∫ θ in (0 : ℝ)..2 * Real.pi, (i.map fun p => Real.cos ((intOf p : ℝ) * θ)).prod) ≠ 0

open Classical in
/-- COSINE PRODUCT INTEGRATION as a decision problem over bitstrings. -/
noncomputable def cosineProductIntegrationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CosineProductIntegrationInstance) x with
  | some i => decide (WellFormed i ∧ CosineProductIntegrationFeasible i)
  | none => false

/-- **COSINE PRODUCT INTEGRATION is NP-complete.** Source: Garey and Johnson (1979), [AN14];
Plaisted (1976). -/
public theorem_wanted cosineProductIntegration_npComplete :
    cosineProductIntegrationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cosineProductIntegrationDec

end MetaMathlibExt.Complexity.NPComplete.CosineProductIntegration
