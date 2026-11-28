/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL DELETE-FREE PLANNING: definitions

Source:
T. Bylander, "The computational complexity of propositional STRIPS planning", Artificial
Intelligence 69 (1994), 165-204, doi:10.1016/0004-3702(94)90081-7;
J. Hoffmann and B. Nebel, "The FF planning system: fast plan generation through heuristic
search", Journal of Artificial Intelligence Research 14 (2001), 253-302, doi:10.1613/jair.855,
Section 3 (STRIPS actions, relaxed planning tasks without delete lists, plans) and Section 4
(computing the optimal length of such a plan is NP-hard, Bylander 1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalDeleteFreePlanning

/-- An instance: the actions `(pre(o), add(o))`, the initial state `I`, the goals `G`, and the
bound `K`. -/
abbrev OptimalDeleteFreePlanningInstance := List (List ℕ × List ℕ) × List ℕ × List ℕ × ℕ

/-- `Result(S, ⟨o⟩)`: `S ∪ add(o)` if `pre(o) ⊆ S`, undefined otherwise. -/
def applyAction (S : Finset ℕ) (o : List ℕ × List ℕ) : Option (Finset ℕ) :=
  if o.1.toFinset ⊆ S then some (S ∪ o.2.toFinset) else none

/-- `Result(S, ⟨o₁, …, oₙ⟩)`: the actions applied from left to right, undefined as soon as one
of them is inapplicable. -/
def result (O : List (List ℕ × List ℕ)) (S : Finset ℕ) : List (Fin O.length) → Option (Finset ℕ)
  | [] => some S
  | a :: p => (applyAction S O[a]).bind fun S' => result O S' p

/-- Some plan of at most `K` actions of `O`, applied to `I`, reaches a state containing `G`. -/
def OptimalDeleteFreePlanningFeasible (i : OptimalDeleteFreePlanningInstance) : Prop :=
  ∃ p : List (Fin i.1.length), p.length ≤ i.2.2.2 ∧
    ∃ S, result i.1 i.2.1.toFinset p = some S ∧ i.2.2.1.toFinset ⊆ S

open Classical in
/-- OPTIMAL DELETE-FREE PLANNING as a decision problem over bitstrings. -/
noncomputable def optimalDeleteFreePlanningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimalDeleteFreePlanningInstance) x with
  | some i => decide (OptimalDeleteFreePlanningFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OptimalDeleteFreePlanning
