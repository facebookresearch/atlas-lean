/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSATISFYING LINEAR SUBSYSTEM: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM UNSATISFYING LINEAR SUBSYSTEM (the optimization problem whose decision version is
stated here);
E. Amaldi and V. Kann, "The complexity and approximability of finding maximum feasible subsystems
of linear relations", Theoretical Computer Science 147 (1995), 181-210,
doi:10.1016/0304-3975(94)00254-G (MAX FLS with equations is NP-hard);
E. Amaldi and V. Kann, "On the approximability of minimizing nonzero variables or unsatisfied
relations in linear systems", Theoretical Computer Science 209 (1998), 237-260,
doi:10.1016/S0304-3975(97)00115-1 (approximability of Min ULR).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquationsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsatisfyingLinearSubsystem

open MetaMathlibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquations
  (MinimumWeightSolutionToLinearEquationsInstance intOf)

/-- The value `a · x` of the left-hand side of the equation with row `a` at `x`. -/
def rowValue {n : ℕ} (a : List (ℕ × ℕ)) (x : Fin n → ℚ) : ℚ :=
  ∑ j : Fin n, (intOf (a.getD j (0, 0)) : ℚ) * x j

/-- Well-formedness of an instance: every row has `n` entries, and `0 < K ≤ m`. -/
def WellFormed (i : MinimumWeightSolutionToLinearEquationsInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1.length = i.1) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- Some rational `x` leaves at most `K` equations unsatisfied: the equations `(a, β)` with
`a · x ≠ β` number at most `K`. -/
def UnsatisfyingLinearSubsystemFeasible (i : MinimumWeightSolutionToLinearEquationsInstance) :
    Prop :=
  ∃ x : Fin i.1 → ℚ, (i.2.1.filter fun e => rowValue e.1 x ≠ intOf e.2).length ≤ i.2.2

open Classical in
/-- UNSATISFYING LINEAR SUBSYSTEM as a decision problem over bitstrings. -/
noncomputable def unsatisfyingLinearSubsystemDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumWeightSolutionToLinearEquationsInstance) x with
  | some i => decide (WellFormed i ∧ UnsatisfyingLinearSubsystemFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnsatisfyingLinearSubsystem
