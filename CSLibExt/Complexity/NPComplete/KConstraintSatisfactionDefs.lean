/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-CONSTRAINT SATISFACTION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM K-CONSTRAINT SATISFACTION (APX-complete; transformation from
MAXIMUM 2-SATISFIABILITY);
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1
(MAXIMUM 2-SATISFIABILITY is NP-complete); M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO5]
MAX 2-SATISFIABILITY.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.Minimum3DnfSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KConstraintSatisfaction

/-- An instance: the number `n` of variables, the conjunctive clauses as lists of literals
`(variable, polarity)`, and the bound `K`. -/
abbrev KConstraintSatisfactionInstance := ℕ × List (List (ℕ × Bool)) × ℕ

/-- Well-formedness of an instance for the constant `k`: every clause has at most `k`
literals, every literal names one of `u₀, ..., u_{n-1}`, and `K` is positive. -/
def WellFormed (k : ℕ) (i : KConstraintSatisfactionInstance) : Prop :=
  (∀ t ∈ i.2.1, t.length ≤ k ∧ ∀ l ∈ t, l.1 < i.1) ∧ 0 < i.2.2

/-- Some truth assignment satisfies at least `K` clauses. -/
def KConstraintSatisfactionFeasible (i : KConstraintSatisfactionInstance) : Prop :=
  ∃ σ : ℕ → Bool, i.2.2 ≤ Minimum3DnfSatisfiability.satisfiedCount σ i.2.1

open Classical in
/-- K-CONSTRAINT SATISFACTION with clauses of at most `k` literals as a decision problem over
bitstrings. -/
noncomputable def kConstraintSatisfactionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KConstraintSatisfactionInstance) x with
  | some i => decide (WellFormed k i ∧ KConstraintSatisfactionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KConstraintSatisfaction
