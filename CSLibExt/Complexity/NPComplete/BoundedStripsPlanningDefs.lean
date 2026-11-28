/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED STRIPS PLANNING (plan length in unary): definitions

Source:
T. Bylander, "The computational complexity of propositional STRIPS planning", Artificial
Intelligence 69 (1994), 165-204, doi:10.1016/0004-3702(94)90081-7, Section 2.1 (propositional
STRIPS planning, `PLANMIN`) and Theorem 4.2 (`3SAT` reduces to `PLANMIN` with bound
`k = 2m + n`);
D. Speck, M. Hecher, D. Gnad, J. K. Fichte, and A. B. Corrêa, "Counting and reasoning with
plans", Proceedings of the AAAI Conference on Artificial Intelligence 39 (2025),
doi:10.1609/aaai.v39i25.34871; extended version arXiv:2502.00145, Section 2 (bounded plan
existence with a polynomially bounded plan length is NP-complete, Bylander 1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedStripsPlanning

/-- An operator `Pre ⇒ Post`, given as `(o₊, o₋, o⁺, o⁻)`: positive preconditions, negative
preconditions, positive postconditions (add list), negative postconditions (delete list). -/
abbrev Operator := List ℕ × List ℕ × List ℕ × List ℕ

/-- An instance: the number `N` of conditions (`P = {0, …, N - 1}`), the operators `O`, the initial
state `I`, the goals `(G₊, G₋)`, and the bound `k` written in unary. -/
abbrev BoundedStripsPlanningInstance :=
  ℕ × List Operator × List ℕ × (List ℕ × List ℕ) × List Bool

/-- A satisfiable conjunction of the positive conditions `pos` and the negative conditions `neg`
over `{0, …, N - 1}`: every condition lies in `P`, and no condition is both required and
forbidden. -/
def SatisfiableConj (N : ℕ) (pos neg : List ℕ) : Prop :=
  (∀ p ∈ pos, p < N) ∧ (∀ p ∈ neg, p < N) ∧ ∀ p ∈ pos, p ∉ neg

/-- Well-formedness: every operator's `Pre` and `Post` are satisfiable conjunctions over `P`,
`I ⊆ P`, the goals are a satisfiable conjunction over `P`, and the bound is written in unary as
`[true, …, true]`. -/
def WellFormed (i : BoundedStripsPlanningInstance) : Prop :=
  (∀ o ∈ i.2.1, SatisfiableConj i.1 o.1 o.2.1 ∧ SatisfiableConj i.1 o.2.2.1 o.2.2.2) ∧
    (∀ p ∈ i.2.2.1, p < i.1) ∧ SatisfiableConj i.1 i.2.2.2.1.1 i.2.2.2.1.2 ∧
    ∀ b ∈ i.2.2.2.2, b = true

/-- `Result(S, (o))`: `(S ∪ o⁺) \ o⁻` if `o₊ ⊆ S` and `o₋ ∩ S = ∅`, and `S` otherwise. -/
def result (S : Finset ℕ) (o : Operator) : Finset ℕ :=
  if o.1.toFinset ⊆ S ∧ Disjoint o.2.1.toFinset S then (S ∪ o.2.2.1.toFinset) \ o.2.2.2.toFinset
  else S

/-- `Result(S, (o₁, …, oₙ))`: the operators applied to `S` from left to right. -/
def resultSeq (S : Finset ℕ) (plan : List Operator) : Finset ℕ :=
  plan.foldl result S

/-- `S` is a goal state: `G₊ ⊆ S` and `G₋ ∩ S = ∅`. -/
def IsGoalState (G : List ℕ × List ℕ) (S : Finset ℕ) : Prop :=
  G.1.toFinset ⊆ S ∧ Disjoint G.2.toFinset S

/-- Some sequence of at most `k` operators of `O` (positions in the operator list, repetitions
allowed) takes `I` to a goal state. -/
def BoundedStripsPlanningFeasible (i : BoundedStripsPlanningInstance) : Prop :=
  ∃ plan : List (Fin i.2.1.length), plan.length ≤ i.2.2.2.2.length ∧
    IsGoalState i.2.2.2.1 (resultSeq i.2.2.1.toFinset (plan.map fun a => i.2.1[a]))

open Classical in
/-- BOUNDED STRIPS PLANNING (plan length in unary) as a decision problem over bitstrings. -/
noncomputable def boundedStripsPlanningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedStripsPlanningInstance) x with
  | some i => decide (WellFormed i ∧ BoundedStripsPlanningFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedStripsPlanning
