/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EDGE-COST FLOW: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND32] MINIMUM EDGE-COST FLOW (p. 214;
credited there to S. Even and D. S. Johnson, 1977, unpublished; transformation from X3C).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlow

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), the arcs
`(tail, head, capacity, price)`, `s`, `t`, the requirement `R`, and the bound `B`. -/
abbrev MinimumEdgeCostFlowInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ

/-- The arcs `(u, v)` of the arc records. -/
def arcs (i : MinimumEdgeCostFlowInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun a => (a.1, a.2.1)

/-- The capacity of the first arc record from `u` to `v`, and `0` when there is no such record;
for a well-formed instance this is the capacity `c(u, v)` of the arc. -/
def capacity (i : MinimumEdgeCostFlowInstance) (u v : ℕ) : ℕ :=
  ((i.2.1.find? fun a => a.1 = u ∧ a.2.1 = v).map fun a => a.2.2.1).getD 0

/-- The price of the first arc record from `u` to `v`, and `0` when there is no such record;
for a well-formed instance this is the price `p(u, v)` of the arc. -/
def price (i : MinimumEdgeCostFlowInstance) (u v : ℕ) : ℕ :=
  ((i.2.1.find? fun a => a.1 = u ∧ a.2.1 = v).map fun a => a.2.2.2).getD 0

/-- Well-formedness of an instance: the arc records describe a directed graph on
`0, ..., n - 1` (endpoints in range, no self-loops, no repeated arcs), every capacity is positive,
`s` and `t` are distinct vertices, and `R` and `B` are positive. -/
def WellFormed (i : MinimumEdgeCostFlowInstance) : Prop :=
  ((arcs i).Nodup ∧ ∀ a ∈ arcs i, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    (∀ a ∈ i.2.1, 0 < a.2.2.1) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧ 0 < i.2.2.2.2.1 ∧ 0 < i.2.2.2.2.2

/-- An integral flow within the capacities, conserved at every vertex other than `s` and `t`,
with net flow into `t` at least `R`, whose arcs carrying nonzero flow have total price at most
`B`. -/
def MinimumEdgeCostFlowFeasible (i : MinimumEdgeCostFlowInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1), ∃ f : Fin i.1 → Fin i.1 → ℕ,
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩
        (fun u v => (f u v : ℝ)) ∧
      (i.2.2.2.2.1 : ℝ) ≤ (∑ u, (f u ⟨i.2.2.2.1, ht⟩ : ℝ)) - ∑ w, (f ⟨i.2.2.2.1, ht⟩ w : ℝ) ∧
      (∑ u, ∑ v, if f u v = 0 then 0 else price i u v) ≤ i.2.2.2.2.2

open Classical in
/-- MINIMUM EDGE-COST FLOW as a decision problem over bitstrings. -/
noncomputable def minimumEdgeCostFlowDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumEdgeCostFlowInstance) x with
  | some i => decide (WellFormed i ∧ MinimumEdgeCostFlowFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlow
