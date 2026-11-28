/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TEMPORAL CONSTRAINT SATISFACTION: definitions

Source:
R. Dechter, I. Meiri, and J. Pearl, "Temporal constraint networks", Artificial
Intelligence 49 (1991), 61-95, doi:10.1016/0004-3702(91)90006-6, Section 2
(TCSP) and Theorem 4.1 (deciding consistency of a TCSP is NP-hard; credited there
to E. Davis, private communication, 1989).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction

/-- A rational endpoint `(p, m, d)`, standing for `(p - m) / d`. -/
abbrev Endpoint := ℕ × ℕ × ℕ

/-- The value `(p - m) / d` of an endpoint. -/
def Endpoint.val (e : Endpoint) : ℚ := ((e.1 : ℤ) - e.2.1 : ℚ) / e.2.2

/-- An instance: the number `n` of variables, unary constraints `(i, intervals)`, and binary
constraints `(i, j, intervals)`, each interval a pair of endpoints `(a, b)`. -/
abbrev TemporalConstraintSatisfactionInstance :=
  ℕ × List (ℕ × List (Endpoint × Endpoint)) × List (ℕ × ℕ × List (Endpoint × Endpoint))

/-- An interval `[a, b]` is well formed: positive denominators and `a ≤ b`. -/
def IntervalOK (I : Endpoint × Endpoint) : Prop :=
  0 < I.1.2.2 ∧ 0 < I.2.2.2 ∧ I.1.val ≤ I.2.val

/-- Well-formedness of an instance: every constraint is on variables `< n`, and every interval
is well formed. -/
def WellFormed (i : TemporalConstraintSatisfactionInstance) : Prop :=
  (∀ c ∈ i.2.1, c.1 < i.1 ∧ ∀ I ∈ c.2, IntervalOK I) ∧
    ∀ c ∈ i.2.2, c.1 < i.1 ∧ c.2.1 < i.1 ∧ ∀ I ∈ c.2.2, IntervalOK I

/-- A real value lies in one of the intervals of a constraint. -/
def InSome (x : ℝ) (Is : List (Endpoint × Endpoint)) : Prop :=
  ∃ I ∈ Is, (I.1.val : ℝ) ≤ x ∧ x ≤ (I.2.val : ℝ)

/-- The network is consistent: some real assignment `X` satisfies every unary constraint
(`Xᵢ` in one of its intervals) and every binary constraint (`Xⱼ - Xᵢ` in one of its
intervals). -/
def TemporalConstraintSatisfactionFeasible
    (i : TemporalConstraintSatisfactionInstance) : Prop :=
  ∃ X : ℕ → ℝ, (∀ c ∈ i.2.1, InSome (X c.1) c.2) ∧
    ∀ c ∈ i.2.2, InSome (X c.2.1 - X c.1) c.2.2

open Classical in
/-- TEMPORAL CONSTRAINT SATISFACTION as a decision problem over bitstrings. -/
noncomputable def temporalConstraintSatisfactionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TemporalConstraintSatisfactionInstance) x with
  | some i => decide (WellFormed i ∧ TemporalConstraintSatisfactionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction
