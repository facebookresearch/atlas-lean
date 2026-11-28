/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITY ASSIGNMENT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR7] CAPACITY ASSIGNMENT
(p. 227; transformation from SUBSET SUM), credited there to [Van Sickle and Chandy, 1977],
"The complexity of computer network design problems", listed in the book's bibliography as an
unpublished manuscript.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacityAssignment

/-- An instance: the capacity list `M`, for each link `c` the list of pairs
`(g(c, x), d(c, x))` over the capacities `x` of `M` in order, and the bounds `K` and `J`. -/
abbrev CapacityAssignmentInstance := List ℕ × List (List (ℕ × ℕ)) × ℕ × ℕ

/-- The pair `(g(c, x), d(c, x))` for link `c` and the capacity `x` at position `k` of `M`. -/
def entry (i : CapacityAssignmentInstance) (c k : ℕ) : ℕ × ℕ :=
  (i.2.1.getD c []).getD k (0, 0)

/-- Well-formedness of an instance: the capacities are distinct and positive; every link lists
one pair per capacity, with positive cost and positive delay penalty; for every link and
capacities `M[a] < M[b]`, `g(c, M[a]) ≤ g(c, M[b])` and `d(c, M[a]) ≥ d(c, M[b])`; and `K` and
`J` are positive. -/
def WellFormed (i : CapacityAssignmentInstance) : Prop :=
  i.1.Nodup ∧ (∀ x ∈ i.1, 0 < x) ∧
    (∀ row ∈ i.2.1, row.length = i.1.length ∧ ∀ e ∈ row, 0 < e.1 ∧ 0 < e.2) ∧
    (∀ c < i.2.1.length, ∀ a < i.1.length, ∀ b < i.1.length, i.1.getD a 0 < i.1.getD b 0 →
      (entry i c a).1 ≤ (entry i c b).1 ∧ (entry i c b).2 ≤ (entry i c a).2) ∧
    0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- Some assignment `σ` of a capacity to every link has total cost at most `K` and total delay
penalty at most `J`. -/
def CapacityAssignmentFeasible (i : CapacityAssignmentInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length,
    ∑ c : Fin i.2.1.length, (entry i c (σ c)).1 ≤ i.2.2.1 ∧
      ∑ c : Fin i.2.1.length, (entry i c (σ c)).2 ≤ i.2.2.2

open Classical in
/-- CAPACITY ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def capacityAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacityAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ CapacityAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CapacityAssignment
