/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MULTIPLE KNAPSACK.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack

/-!
# MULTIPLE KNAPSACK is NP-complete

Items with weights and values, several knapsacks with capacities, and a target value. Each item
is assigned to at most one knapsack (assignment equal to the number of knapsacks means
omitted). The question is whether the assigned items fit in their knapsacks and have total
value at least the target.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A multiple-knapsack instance: items as (weight, value) pairs, knapsack capacities, target
value. -/
abbrev MultipleKnapsackInstance := List (ℕ × ℕ) × List ℕ × ℕ

/-- An assignment fitting the knapsacks of total value at least the target. -/
def MultipleKnapsackFeasible
    (i : MultipleKnapsackInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧
    (∀ j < i.1.length, assign.getD j 0 ≤ i.2.1.length) ∧
    (∀ b < i.2.1.length,
      (Finset.range i.1.length).sum (fun j =>
        if assign.getD j 0 = b then (i.1.getD j (0, 0)).1 else 0) ≤
        i.2.1.getD b 0) ∧
    i.2.2 ≤ (Finset.range i.1.length).sum (fun j =>
      if assign.getD j 0 < i.2.1.length then (i.1.getD j (0, 0)).2 else 0)

open Classical in
/-- MULTIPLE KNAPSACK as a decision problem over bitstrings. -/
noncomputable def multipleKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleKnapsackInstance) x with
  | some i => decide (MultipleKnapsackFeasible i)
  | none => false

/-- **MULTIPLE KNAPSACK is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), MULTIPLE KNAPSACK. -/
public theorem_wanted multipleKnapsack_npComplete :
    multipleKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
