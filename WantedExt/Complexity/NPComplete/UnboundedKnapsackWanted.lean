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

/-- **Unbounded knapsack instances.** An instance of the unbounded knapsack problem is a triple
$(I, C, K)$ of a finite list $I = ((s_1, v_1), \dots, (s_m, v_m))$ of items, where item $j$ has
weight $s_j \in \mathbb{N}$ and value $v_j \in \mathbb{N}$, a capacity $C \in \mathbb{N}$ and a
target value $K \in \mathbb{N}$. -/
abbrev UnboundedKnapsackInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- **Feasible unbounded knapsack instances.** An unbounded knapsack instance with items
$(s_1, v_1), \dots, (s_m, v_m)$, capacity $C$ and target value $K$ is feasible when there are
multiplicities $c_1, \dots, c_m \in \mathbb{N}$ with $\sum_{j=1}^{m} c_j s_j \le C$ and
$\sum_{j=1}^{m} c_j v_j \ge K$. -/
def UnboundedKnapsackFeasible
    (i : UnboundedKnapsackInstance) : Prop :=
  ∃ mult : List ℕ, mult.length = i.1.length ∧
    (Finset.range i.1.length).sum
      (fun j => mult.getD j 0 * (i.1.getD j (0, 0)).1) ≤ i.2.1 ∧
    i.2.2 ≤ (Finset.range i.1.length).sum
      (fun j => mult.getD j 0 * (i.1.getD j (0, 0)).2)

open Classical in
/-- **Unbounded knapsack as a decision problem.** The unbounded knapsack problem is the decision
problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of unbounded knapsack instances, to a feasible instance. Bitstrings that fail to decode
are rejected. -/
noncomputable def unboundedKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedKnapsackInstance) x with
  | some i => decide (UnboundedKnapsackFeasible i)
  | none => false

/-- **UNBOUNDED KNAPSACK is NP-complete.** The unbounded knapsack decision problem belongs to NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), UNBOUNDED KNAPSACK. -/
public theorem_wanted unboundedKnapsack_npComplete :
    unboundedKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unboundedKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.UnboundedKnapsack
