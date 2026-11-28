/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BINARY QUADRATIC DIOPHANTINE EQUATIONS: definitions

Source:
J. C. Lagarias, "Succinct certificates for the solvability of binary quadratic Diophantine
equations", Proceedings of the 20th Annual Symposium on Foundations of Computer Science (FOCS
1979), 47-54, doi:10.1109/SFCS.1979.40 (full version arXiv:math/0611209, Theorem 1.2(ii): the
set of `a, b, c, d, e, f ∈ ℤ` such that `a x₁² + b x₁ x₂ + c x₂² + d x₁ + e x₂ + f = 0` has a
solution in nonnegative integers is in NP, and with Manders and Adleman's result "testing
membership in the sets Σ₁ and Σ₂ in Theorem 1.2 are both NP-complete");
K. L. Manders and L. Adleman, "NP-complete decision problems for binary quadratics", Journal of
Computer and System Sciences 16 (1978), 168-184, doi:10.1016/0022-0000(78)90044-2 (the special
form `α x² + β y - γ = 0` with natural-number solutions is NP-complete);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [AN8] QUADRATIC DIOPHANTINE EQUATIONS (the
special form).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Ring.Int.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryQuadraticDiophantine

/-- An instance: the coefficients `a, b, c, d, e, f`, each a pair `(positive part, negative
part)`. -/
abbrev BinaryQuadraticDiophantineInstance :=
  (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- The integer `p - n` denoted by the pair `(p, n)`. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- The value `a x₁² + b x₁ x₂ + c x₂² + d x₁ + e x₂ + f` of the instance's quadratic. -/
def eval (i : BinaryQuadraticDiophantineInstance) (x₁ x₂ : ℤ) : ℤ :=
  intOf i.1 * x₁ ^ 2 + intOf i.2.1 * x₁ * x₂ + intOf i.2.2.1 * x₂ ^ 2 + intOf i.2.2.2.1 * x₁ +
    intOf i.2.2.2.2.1 * x₂ + intOf i.2.2.2.2.2

/-- The equation has a solution in nonnegative integers. -/
def BinaryQuadraticDiophantineFeasible (i : BinaryQuadraticDiophantineInstance) : Prop :=
  ∃ x₁ x₂ : ℕ, eval i x₁ x₂ = 0

open Classical in
/-- BINARY QUADRATIC DIOPHANTINE EQUATIONS as a decision problem over bitstrings. Every decoded
instance is well formed. -/
noncomputable def binaryQuadraticDiophantineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BinaryQuadraticDiophantineInstance) x with
  | some i => decide (BinaryQuadraticDiophantineFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BinaryQuadraticDiophantine
