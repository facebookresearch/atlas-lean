/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COSINE PRODUCT INTEGRATION (nonzero form) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN14] COSINE PRODUCT
INTEGRATION (stated there with `= 0`; this is the nonzero form);
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard",
Proc. 17th Annual Symposium on Foundations of Computer Science (1976), 264-267,
doi:10.1109/SFCS.1976.29; journal version SIAM Journal on Computing 7 (1978),
458-464, doi:10.1137/0207036;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9
(PARTITION);
S. Rass, "Towards a physical oracle for the Partition problem using analogue
computing", arXiv:1705.01826 (2017), Section 1 (the Fourier identity below and
its link to PARTITION).
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
# COSINE PRODUCT INTEGRATION (nonzero form) is NP-complete

INSTANCE: a sequence `(a₁, ..., aₙ)` of integers. QUESTION: is
`∫₀^{2π} ∏ᵢ cos(aᵢ θ) dθ ≠ 0`?

Garey and Johnson's [AN14] asks whether this integral is `= 0`. That question is the complement
of the one stated here; this module states the nonzero form, which is the NP-complete one.

Derivation from PARTITION: writing `cos(aθ) = (e^{iaθ} + e^{-iaθ}) / 2`, the integral equals
`2π · 2⁻ⁿ` times the number of sign vectors `ε ∈ {±1}ⁿ` with `∑ εᵢ aᵢ = 0` (Rass 2017,
Section 1). So it is nonzero exactly when the `|aᵢ|` split into two parts of equal sum, which
is PARTITION (Karp 1972) up to signs; Garey and Johnson credit the transformation from PARTITION
to Plaisted (1976). Guessing the signs puts the nonzero form in NP, while the `= 0` form is the
complement of PARTITION, a coNP question.

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
def CosineProductIntegrationNonzeroFeasible (i : CosineProductIntegrationInstance) : Prop :=
  (∫ θ in (0 : ℝ)..2 * Real.pi, (i.map fun p => Real.cos ((intOf p : ℝ) * θ)).prod) ≠ 0

open Classical in
/-- COSINE PRODUCT INTEGRATION (nonzero form) as a decision problem over bitstrings. -/
noncomputable def cosineProductIntegrationNonzeroDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CosineProductIntegrationInstance) x with
  | some i => decide (WellFormed i ∧ CosineProductIntegrationNonzeroFeasible i)
  | none => false

/-- **COSINE PRODUCT INTEGRATION (nonzero form) is NP-complete.** Source: Garey and Johnson
(1979), [AN14] (the `= 0` form); Plaisted (1976); Karp (1972); Rass (2017). -/
public theorem_wanted cosineProductIntegrationNonzero_npComplete :
    cosineProductIntegrationNonzeroDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cosineProductIntegrationNonzeroDec

end MetaMathlibExt.Complexity.NPComplete.CosineProductIntegration
