/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC KNAPSACK is NP-complete

Source:
G. Gallo, P. L. Hammer and B. Simeone, "Quadratic knapsack problems", Mathematical
Programming Study 12 (1980), 132-149, doi:10.1007/BFb0120892;
L. Galli, S. Martello and P. Toth, "The quadratic knapsack problem", European Journal of
Operational Research 326 (2025), 1-12, doi:10.1016/j.ejor.2024.12.032 (Section 2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticKnapsack

/-!
# QUADRATIC KNAPSACK is NP-complete

INSTANCE: `n` items with positive integer weights `w_i`, a positive integer capacity `c`, a
nonnegative integer `n × n` profit matrix `Q = (q_{i,j})`, and a bound `K`. QUESTION: is there
`x ∈ {0, 1}ⁿ` with `∑_i w_i x_i ≤ c` and `∑_i ∑_j q_{i,j} x_i x_j ≥ K`?

This is the decision version of the 0-1 quadratic knapsack problem of Gallo, Hammer and
Simeone, in the form `max xᵀ Q x` subject to the capacity constraint (model (4)-(5) of Galli,
Martello and Toth, where the diagonal `q_{i,i}` holds the profit of item `i` and `q_{i,j} +
q_{j,i}` the extra profit of selecting both `i` and `j`). Galli, Martello and Toth (Section 2)
prove it strongly NP-hard: CLIQUE is the special case with `Q` the adjacency matrix of the
graph, unit weights, `c = k` and `K = k (k - 1)`. Membership in NP: `x` is a certificate.
Binary encoding of all numbers.

Items are `0, ..., n - 1`, where `n` is the length of the weight list, and `x` is given by the
set `S = {i | x_i = 1}`, so `∑_i ∑_j q_{i,j} x_i x_j = ∑_{i ∈ S} ∑_{j ∈ S} q_{i,j}`. Entries
are natural numbers, so `Q` is nonnegative.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the weights `w_0, ..., w_{n-1}`, the capacity `c`, the profit matrix `Q` as a
list of rows, and the bound `K`. -/
abbrev QuadraticKnapsackInstance := List ℕ × ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every weight is positive, the capacity is positive, and
`Q` is an `n × n` matrix, where `n` is the number of items. -/
def WellFormed (i : QuadraticKnapsackInstance) : Prop :=
  (∀ w ∈ i.1, 0 < w) ∧ 0 < i.2.1 ∧ i.2.2.1.length = i.1.length ∧
    ∀ row ∈ i.2.2.1, row.length = i.1.length

/-- Some set `S` of items has total weight at most `c` and profit
`∑_{i ∈ S} ∑_{j ∈ S} q_{i,j}` at least `K`. -/
def QuadraticKnapsackFeasible (i : QuadraticKnapsackInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ k ∈ S, k < i.1.length) ∧ ∑ k ∈ S, i.1.getD k 0 ≤ i.2.1 ∧
    i.2.2.2 ≤ ∑ k ∈ S, ∑ l ∈ S, (i.2.2.1.getD k []).getD l 0

open Classical in
/-- QUADRATIC KNAPSACK as a decision problem over bitstrings. -/
noncomputable def quadraticKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticKnapsackFeasible i)
  | none => false

/-- **QUADRATIC KNAPSACK is NP-complete.** Source: Gallo, Hammer and Simeone (1980); Galli,
Martello and Toth (2025). -/
public theorem_wanted quadraticKnapsack_npComplete :
    quadraticKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticKnapsack
