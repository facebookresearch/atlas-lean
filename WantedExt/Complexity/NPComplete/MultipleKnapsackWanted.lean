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

/-- **Multiple-knapsack instances.** A multiple-knapsack instance consists of a finite list of
items, each a pair $(w, v)$ of natural numbers giving its weight $w$ and value $v$, a finite list
of natural-number knapsack capacities, and a natural-number target value. -/
abbrev MultipleKnapsackInstance := List (ℕ × ℕ) × List ℕ × ℕ

/-- **Feasible multiple-knapsack instances.** Let a multiple-knapsack instance have items
$(w_0, v_0), \dots, (w_{k-1}, v_{k-1})$ (weight, value), knapsack capacities
$c_0, \dots, c_{m-1}$ and target $V$. The instance is feasible when there are
$a_0, \dots, a_{k-1} \in \{0, \dots, m\}$, where $a_j = b < m$ puts item $j$ in knapsack $b$
and $a_j = m$ leaves item $j$ out, such that for every $b < m$ the total weight
$\sum_{j : a_j = b} w_j$ is at most $c_b$, and the total value $\sum_{j : a_j < m} v_j$ is at
least $V$. -/
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
/-- **MULTIPLE KNAPSACK as a decision problem.** The decision problem MULTIPLE KNAPSACK accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a feasible
multiple-knapsack instance. Bitstrings that do not decode are rejected. -/
noncomputable def multipleKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleKnapsackInstance) x with
  | some i => decide (MultipleKnapsackFeasible i)
  | none => false

/-- **MULTIPLE KNAPSACK is NP-complete.** The decision problem MULTIPLE KNAPSACK belongs to NP,
and every decision problem in NP has a polynomial-time many-one reduction to MULTIPLE KNAPSACK.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), MULTIPLE KNAPSACK. -/
public theorem_wanted multipleKnapsack_npComplete :
    multipleKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
