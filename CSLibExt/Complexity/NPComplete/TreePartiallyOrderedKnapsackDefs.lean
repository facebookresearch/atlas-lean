/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIALLY ORDERED KNAPSACK with a tree order: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY ORDERED KNAPSACK,
pp. 247-248 (comment: "General problem is solvable in pseudo-polynomial time if < is a "tree"
partial order [Garey and Johnson, ——].");
D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic
programming technique for trees", Mathematics of Operations Research 8 (1983),
1-14, doi:10.1287/moor.8.1.1 (abstract: the special case where the order is an out-tree "is
still NP-complete").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartiallyOrderedKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreePartiallyOrderedKnapsack

open MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack
  (PartiallyOrderedKnapsackInstance Precedes PartiallyOrderedKnapsackFeasible)

/-- The order of the instance is the order of an out-tree: any two predecessors of an element
are equal or comparable, and some root precedes every other element. -/
def IsTreeOrder (i : PartiallyOrderedKnapsackInstance) : Prop :=
  (∀ u a b : Fin i.1.length, Precedes i a u → Precedes i b u →
      a = b ∨ Precedes i a b ∨ Precedes i b a) ∧
    ∃ r : Fin i.1.length, ∀ u, u ≠ r → Precedes i r u

/-- Well-formedness of an instance: the [MP12] well-formedness, and the order is a tree
order. -/
def WellFormed (i : PartiallyOrderedKnapsackInstance) : Prop :=
  PartiallyOrderedKnapsack.WellFormed i ∧ IsTreeOrder i

open Classical in
/-- PARTIALLY ORDERED KNAPSACK with a tree order as a decision problem over bitstrings. -/
noncomputable def treePartiallyOrderedKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartiallyOrderedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ PartiallyOrderedKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreePartiallyOrderedKnapsack
