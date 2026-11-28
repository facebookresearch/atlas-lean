/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COSINE PRODUCT INTEGRATION (nonzero form): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CosineProductIntegration

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

end MetaMathlibExt.Complexity.NPComplete.CosineProductIntegration
