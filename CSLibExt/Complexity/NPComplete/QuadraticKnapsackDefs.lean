/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC KNAPSACK: definitions

Source:
G. Gallo, P. L. Hammer and B. Simeone, "Quadratic knapsack problems", Mathematical
Programming Study 12 (1980), 132-149, doi:10.1007/BFb0120892;
L. Galli, S. Martello and P. Toth, "The quadratic knapsack problem", European Journal of
Operational Research 326 (2025), 1-12, doi:10.1016/j.ejor.2024.12.032 (Section 2).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticKnapsack

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

end MetaMathlibExt.Complexity.NPComplete.QuadraticKnapsack
