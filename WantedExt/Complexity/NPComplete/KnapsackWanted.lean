/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), KNAPSACK (MP9).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Knapsack

/-!
# KNAPSACK is NP-complete

A 0/1 knapsack instance is a list of items, each a `(weight, value)` pair of natural numbers,
together with a capacity and a target value. The question is whether some sublist of the items
has total weight at most the capacity and total value at least the target. Variant: nonnegative
integers (the Garey-Johnson formulation uses positive integers). Duplicate items are distinct
occurrences, the empty selection is permitted, and a target of zero is always achievable by a
successfully decoded instance. Binary encoding matters: with unary numbers the problem is
solvable in pseudo-polynomial time, hence in P.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A 0/1 knapsack instance: items as (weight, value) pairs, capacity, target value. -/
abbrev KnapsackInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- A selection of item occurrences satisfying the weight and value bounds. The empty
selection is permitted. -/
def KnapsackFeasible
    (i : KnapsackInstance) : Prop :=
  ∃ chosen : List (ℕ × ℕ), chosen.Sublist i.1 ∧
    (chosen.map Prod.fst).sum ≤ i.2.1 ∧ i.2.2 ≤ (chosen.map Prod.snd).sum

open Classical in
/-- KNAPSACK as a decision problem over bitstrings. -/
noncomputable def knapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KnapsackInstance) x with
  | some i => decide (KnapsackFeasible i)
  | none => false

/-- **KNAPSACK is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), KNAPSACK (MP9). -/
public theorem_wanted knapsack_npComplete :
    knapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L knapsackDec

end MetaMathlibExt.Complexity.NPComplete.Knapsack
