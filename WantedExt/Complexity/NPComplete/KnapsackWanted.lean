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

/-- **Knapsack instances.** A 0/1 knapsack instance is a triple $(I, C, T)$ of a list $I$ of items,
each a pair $(w, v)$ of natural numbers giving its weight $w$ and value $v$, a natural-number
capacity $C$, and a natural-number target value $T$. -/
abbrev KnapsackInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- **Feasible knapsack instances.** A knapsack instance $(I, C, T)$, with item list $I$, capacity
$C$ and target value $T$, is feasible when some subsequence of $I$, possibly empty, has total
weight at most $C$ and total value at least $T$. Repeated items in $I$ are distinct occurrences
that can be selected separately. -/
def KnapsackFeasible
    (i : KnapsackInstance) : Prop :=
  ∃ chosen : List (ℕ × ℕ), chosen.Sublist i.1 ∧
    (chosen.map Prod.fst).sum ≤ i.2.1 ∧ i.2.2 ≤ (chosen.map Prod.snd).sum

open Classical in
/-- **The KNAPSACK decision problem.** KNAPSACK is the decision problem that accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a knapsack instance
$(I, C, T)$ for which some subsequence of the item list $I$, possibly empty, has total weight at
most $C$ and total value at least $T$. Bitstrings that do not decode are rejected. -/
noncomputable def knapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KnapsackInstance) x with
  | some i => decide (KnapsackFeasible i)
  | none => false

/-- **KNAPSACK is NP-complete.** The KNAPSACK decision problem is in NP, and every decision
problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), KNAPSACK (MP9). -/
public theorem_wanted knapsack_npComplete :
    knapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L knapsackDec

end MetaMathlibExt.Complexity.NPComplete.Knapsack
