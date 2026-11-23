/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM SATISFYING LINEAR SUBSYSTEM is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM SATISFYING LINEAR SUBSYSTEM (decision version: at least `K` equations satisfied);
E. Amaldi and V. Kann, "The complexity and approximability of finding maximum feasible subsystems
of linear relations", Theoretical Computer Science 147 (1995), 181-210,
doi:10.1016/0304-3975(94)00254-G.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquationsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumSatisfyingLinearSubsystem

open MetaMathlibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquations
  (MinimumWeightSolutionToLinearEquationsInstance intOf)

/-!
# MAXIMUM SATISFYING LINEAR SUBSYSTEM is NP-complete

INSTANCE: a system `Ax = b` of linear equations, where `A` is an integer `m × n` matrix and `b` is
an integer `m`-vector, and a positive integer `K`. QUESTION: is there a rational `n`-vector
`x ∈ ℚⁿ` that satisfies at least `K` of the `m` equations?

The instance type and the integer encoding are those of
`WantedExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquationsWanted`, reused here: the
number `n` of variables, the list of the `m` equations, each a pair `(aᵢ, bᵢ)` of the `i`-th row
of `A` (a list of `n` integers) and the right-hand side, and the bound `K`. An integer is a pair
of naturals `(positive part, negative part)` representing their difference (`intOf`). The rows are
listed with repetition, so a repeated equation counts once per occurrence, as a row of `A` does.
Numbers are encoded in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MAXIMUM SATISFYING LINEAR SUBSYSTEM is NP-complete.** Source: Crescenzi and Kann, MAXIMUM
SATISFYING LINEAR SUBSYSTEM; Amaldi and Kann (1995). -/
public theorem_wanted maximumSatisfyingLinearSubsystem_npComplete :
    maximumSatisfyingLinearSubsystemDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumSatisfyingLinearSubsystemDec

end MetaMathlibExt.Complexity.NPComplete.MaximumSatisfyingLinearSubsystem
