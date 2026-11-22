/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), UNBOUNDED KNAPSACK.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedKnapsack

/-!
# UNBOUNDED KNAPSACK is NP-complete

Items with weights and values, a capacity, and a target value, with each item reusable any
number of times. The question is whether multiplicities (a list of natural numbers, binary-
sized) achieve total weight at most the capacity and total value at least the target.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An unbounded-knapsack instance: items as (weight, value) pairs, capacity, target value. -/
abbrev UnboundedKnapsackInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- Multiplicities meeting the weight and value bounds. -/
def UnboundedKnapsackFeasible
    (i : UnboundedKnapsackInstance) : Prop :=
  ∃ mult : List ℕ, mult.length = i.1.length ∧
    (Finset.range i.1.length).sum
      (fun j => mult.getD j 0 * (i.1.getD j (0, 0)).1) ≤ i.2.1 ∧
    i.2.2 ≤ (Finset.range i.1.length).sum
      (fun j => mult.getD j 0 * (i.1.getD j (0, 0)).2)

open Classical in
/-- UNBOUNDED KNAPSACK as a decision problem over bitstrings. -/
noncomputable def unboundedKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedKnapsackInstance) x with
  | some i => decide (UnboundedKnapsackFeasible i)
  | none => false

/-- **UNBOUNDED KNAPSACK is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), UNBOUNDED KNAPSACK. -/
public theorem_wanted unboundedKnapsack_npComplete :
    unboundedKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unboundedKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.UnboundedKnapsack
