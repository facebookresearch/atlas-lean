/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TEMPORAL CONSTRAINT SATISFACTION is NP-complete

Source:
R. Dechter, I. Meiri, and J. Pearl, "Temporal constraint networks", Artificial
Intelligence 49 (1991), 61-95, doi:10.1016/0004-3702(91)90006-6, Section 2
(TCSP) and Theorem 4.1 (deciding consistency of a TCSP is NP-hard; credited there
to E. Davis, private communication, 1989).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction

/-!
# TEMPORAL CONSTRAINT SATISFACTION is NP-complete

INSTANCE: time-point variables `X₁, ..., Xₙ` with continuous domains, and constraints, each a
finite set of closed intervals `{[a₁, b₁], ..., [aₖ, bₖ]}` with rational endpoints: a unary
constraint on `Xᵢ` represents `(a₁ ≤ Xᵢ ≤ b₁) ∨ ... ∨ (aₖ ≤ Xᵢ ≤ bₖ)`, and a binary constraint on
`(Xᵢ, Xⱼ)` represents `(a₁ ≤ Xⱼ - Xᵢ ≤ b₁) ∨ ... ∨ (aₖ ≤ Xⱼ - Xᵢ ≤ bₖ)`. QUESTION: is the network
consistent, i.e. is there an assignment of real values to the variables satisfying all
constraints?

Variables are `0, ..., n - 1`. A rational endpoint is a triple `(p, m, d)` standing for
`(p - m) / d` with `d > 0` (`Endpoint.val`). Dechter, Meiri and Pearl assume constraints are
given with pairwise disjoint intervals; overlapping intervals denote the same disjunction, so
that canonical form is not required here. The problem is in NP because choosing one interval per
constraint leaves a simple temporal problem, decidable in polynomial time (their Section 3), and
NP-hard by their Theorem 4.1, a reduction from graph 3-coloring with integer point intervals.
Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TEMPORAL CONSTRAINT SATISFACTION is NP-complete.** Source: Dechter, Meiri, and Pearl (1991),
Theorem 4.1. -/
public theorem_wanted temporalConstraintSatisfaction_npComplete :
    temporalConstraintSatisfactionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L temporalConstraintSatisfactionDec

end MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction
