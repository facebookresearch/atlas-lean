/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM SATISFYING LINEAR SUBSYSTEM: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM SATISFYING LINEAR SUBSYSTEM (decision version: at least `K` equations satisfied);
E. Amaldi and V. Kann, "The complexity and approximability of finding maximum feasible subsystems
of linear relations", Theoretical Computer Science 147 (1995), 181-210,
doi:10.1016/0304-3975(94)00254-G.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquationsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumSatisfyingLinearSubsystem

open MetaMathlibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquations
  (MinimumWeightSolutionToLinearEquationsInstance intOf)

/-- Well-formedness of an instance: every row of `A` has `n` entries, and `K` is positive. -/
def WellFormed (i : MinimumWeightSolutionToLinearEquationsInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1.length = i.1) ∧ 0 < i.2.2

/-- Some rational `n`-vector `x` satisfies at least `K` of the equations `aᵢ · x = bᵢ`. -/
def MaximumSatisfyingLinearSubsystemFeasible
    (i : MinimumWeightSolutionToLinearEquationsInstance) : Prop :=
  ∃ x : Fin i.1 → ℚ, i.2.2 ≤ i.2.1.countP fun e =>
    decide (∑ j : Fin i.1, (intOf (e.1.getD j (0, 0)) : ℚ) * x j = intOf e.2)

open Classical in
/-- MAXIMUM SATISFYING LINEAR SUBSYSTEM as a decision problem over bitstrings. -/
noncomputable def maximumSatisfyingLinearSubsystemDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumWeightSolutionToLinearEquationsInstance) x with
  | some i => decide (WellFormed i ∧ MaximumSatisfyingLinearSubsystemFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumSatisfyingLinearSubsystem
