/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GOOD SIMULTANEOUS DIOPHANTINE APPROXIMATION: definitions

Source:
J. C. Lagarias, "The computational complexity of simultaneous Diophantine approximation
problems", SIAM Journal on Computing 14 (1985), 196-209, doi:10.1137/0214016;
F. Eisenbrand and T. Rothvoß, "Recent hardness results for periodic uni-processor scheduling",
Dagstuhl Seminar Proceedings 10071, Scheduling (2010), Section 2, problem (1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Floor

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimultaneousDiophantineApproximation

/-- A rational number: the positive and negative parts of its numerator, and its denominator. -/
abbrev RatCode := (ℕ × ℕ) × ℕ

/-- The value of a rational code. -/
def RatCode.val (q : RatCode) : ℚ := ((q.1.1 : ℤ) - q.1.2 : ℤ) / (q.2 : ℚ)

/-- An instance: the rationals `α₁, …, αₙ`, the bound `N`, and `ε = s₁/s₂` as `(s₁, s₂)`. -/
abbrev SimultaneousDiophantineApproximationInstance := List RatCode × ℕ × (ℕ × ℕ)

/-- Well-formedness: the dimension `n` is at least `1` (the maximum ranges over
`i = 1, …, n`), every denominator is positive, and `ε = s₁/s₂` is a positive rational. -/
def WellFormed (i : SimultaneousDiophantineApproximationInstance) : Prop :=
  i.1 ≠ [] ∧ (∀ a ∈ i.1, 0 < a.2) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- Some `Q ∈ {1, …, N}` puts every `Q αᵢ` within `ε` of its closest integer. -/
def SimultaneousDiophantineApproximationFeasible
    (i : SimultaneousDiophantineApproximationInstance) : Prop :=
  ∃ Q : ℕ, 1 ≤ Q ∧ Q ≤ i.2.1 ∧
    ∀ a ∈ i.1, |(round ((Q : ℚ) * a.val) : ℚ) - (Q : ℚ) * a.val| ≤ (i.2.2.1 : ℚ) / i.2.2.2

open Classical in
/-- GOOD SIMULTANEOUS DIOPHANTINE APPROXIMATION as a decision problem over bitstrings. -/
noncomputable def simultaneousDiophantineApproximationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimultaneousDiophantineApproximationInstance) x with
  | some i => decide (WellFormed i ∧ SimultaneousDiophantineApproximationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimultaneousDiophantineApproximation
