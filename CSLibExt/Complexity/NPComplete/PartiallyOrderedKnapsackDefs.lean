/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIALLY ORDERED KNAPSACK: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY
ORDERED KNAPSACK;
D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic
programming technique for trees", Mathematics of Operations Research 8 (1983),
1-14, doi:10.1287/moor.8.1.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack

/-- An instance: the (size, value) pairs of the elements `u₀, …, u_{n-1}`, the pairs `(a, b)`
with `uₐ < u_b`, and the bounds `B` and `K`. -/
abbrev PartiallyOrderedKnapsackInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × ℕ

/-- The order of the instance as a relation on `Fin n`. -/
def Precedes (i : PartiallyOrderedKnapsackInstance) (a b : Fin i.1.length) : Prop :=
  ((a : ℕ), (b : ℕ)) ∈ i.2.1

/-- The size of an element. -/
def size (i : PartiallyOrderedKnapsackInstance) (u : Fin i.1.length) : ℕ := (i.1.get u).1

/-- The value of an element. -/
def value (i : PartiallyOrderedKnapsackInstance) (u : Fin i.1.length) : ℕ := (i.1.get u).2

/-- Well-formedness of an instance: the order pairs name elements, the relation they list is a
strict partial order, every size and value is positive, and `B` and `K` are positive. -/
def WellFormed (i : PartiallyOrderedKnapsackInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧ IsStrictOrder (Fin i.1.length) (Precedes i) ∧
    (∀ u ∈ i.1, 0 < u.1 ∧ 0 < u.2) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- Some subset `U'`, closed under predecessors, has total size at most `B` and total value at
least `K`. -/
def PartiallyOrderedKnapsackFeasible (i : PartiallyOrderedKnapsackInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), (∀ u ∈ S, ∀ u', Precedes i u' u → u' ∈ S) ∧
    ∑ u ∈ S, size i u ≤ i.2.2.1 ∧ i.2.2.2 ≤ ∑ u ∈ S, value i u

open Classical in
/-- PARTIALLY ORDERED KNAPSACK as a decision problem over bitstrings. -/
noncomputable def partiallyOrderedKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartiallyOrderedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ PartiallyOrderedKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack
