/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSATISFYING LINEAR SUBSYSTEM is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem [MP11]
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquationsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsatisfyingLinearSubsystem

open MetaMathlibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquations
  (MinimumWeightSolutionToLinearEquationsInstance intOf)

/-!
# UNSATISFYING LINEAR SUBSYSTEM is NP-complete

INSTANCE: a system `Ax = b` of linear equations, where `A` is an integer `m × n` matrix and `b`
is an integer `m`-vector, and a positive integer `K ≤ m`. QUESTION: is there a rational
`n`-vector `x ∈ ℚⁿ` such that the number of equations that are not satisfied by `x` is at most
`K`?

This is the decision version of Crescenzi and Kann's MINIMUM UNSATISFYING LINEAR SUBSYSTEM (Min ULR
with equations): a solution leaves at most `K` equations unsatisfied exactly when it satisfies at
least `m - K` of them, so this is also the decision version of MAXIMUM FEASIBLE LINEAR SUBSYSTEM
with equations, which Amaldi and Kann (1995) prove NP-hard (abstract: "Max FLS with =, ⩾ or >
relations is NP-hard"). Their stronger statement for homogeneous systems is not used: for
homogeneous equations `x = 0` satisfies every equation, so the affine system `Ax = b` is the
formulation stated here. Membership in NP: a certificate is the set of satisfied equations, whose
solvability over `ℚ` is decided in polynomial time by Gaussian elimination.

The system is the instance type of `MinimumWeightSolutionToLinearEquationsWanted`, reused: the
number `n` of variables, the list of equations `(a, β)` (row `a` of `A` as `n` encoded integers,
right-hand side `β`), and the bound `K`; each integer is a pair of naturals
`(positive part, negative part)` decoded by `intOf`, as in `ZeroOneILPWanted`. `m` is the length
of the list. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **UNSATISFYING LINEAR SUBSYSTEM is NP-complete.** Source: Crescenzi and Kann, [MP11]; Amaldi
and Kann (1995). -/
public theorem_wanted unsatisfyingLinearSubsystem_npComplete :
    unsatisfyingLinearSubsystemDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unsatisfyingLinearSubsystemDec

end MetaMathlibExt.Complexity.NPComplete.UnsatisfyingLinearSubsystem
