/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED SATISFIABILITY WITH BOUND: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MAXIMUM WEIGHTED SATISFIABILITY WITH BOUND (decision version), citing
P. Crescenzi and A. Panconesi, "Completeness in approximation classes", Information and
Computation 93 (1991), 241-262, doi:10.1016/0890-5401(91)90025-W (APX-complete);
S. A. Cook, "The complexity of theorem-proving procedures", Proc. 3rd Annual ACM Symposium on
Theory of Computing (1971), 151-158, doi:10.1145/800157.805047 (SATISFIABILITY is NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedSatisfiabilityWithBound

/-- An instance: the number `n` of variables `u₀, …, u_{n-1}`, the postfix token list of `F`
(as in `SatisfiabilityOfBooleanExpressionsWanted`), the bound `B`, the weights `w(u₀), …,
w(u_{n-1})`, and the bound `K`. -/
abbrev WeightedSatisfiabilityWithBoundInstance := ℕ × List (ℕ × ℕ) × ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: the token list spells an expression, every variable token
names one of `u₀, …, u_{n-1}`, every connective code names one of the 16 binary connectives,
there is one weight per variable, `B ≤ ∑ w ≤ 2B`, and `K` is positive. -/
def WellFormed (i : WeightedSatisfiabilityWithBoundInstance) : Prop :=
  (SatisfiabilityOfBooleanExpressions.parse i.2.1).isSome ∧
    (∀ t ∈ i.2.1, t.1 = 0 → t.2 < i.1) ∧ (∀ t ∈ i.2.1, t.1 = 1 → t.2 < 16) ∧
      i.2.2.2.1.length = i.1 ∧ i.2.2.1 ≤ i.2.2.2.1.sum ∧ i.2.2.2.1.sum ≤ 2 * i.2.2.1 ∧
        0 < i.2.2.2.2

/-- Some truth assignment `σ` has measure at least `K`: the measure is the total weight of the
variables `uₓ` (`x < n`) with `σ x = true` if `σ` satisfies `F`, and `B` otherwise. Assignments
are functions `ℕ → Bool`; under `WellFormed` only their values on `0, …, n - 1` matter. -/
def WeightedSatisfiabilityWithBoundFeasible (i : WeightedSatisfiabilityWithBoundInstance) :
    Prop :=
  ∃ F, SatisfiabilityOfBooleanExpressions.parse i.2.1 = some F ∧ ∃ σ : ℕ → Bool,
    i.2.2.2.2 ≤
      if F.eval σ then ∑ x ∈ Finset.univ.filter (fun x : Fin i.1 => σ x), i.2.2.2.1.getD x 0
      else i.2.2.1

open Classical in
/-- WEIGHTED SATISFIABILITY WITH BOUND as a decision problem over bitstrings. -/
noncomputable def weightedSatisfiabilityWithBoundDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedSatisfiabilityWithBoundInstance) x with
  | some i => decide (WellFormed i ∧ WeightedSatisfiabilityWithBoundFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedSatisfiabilityWithBound
