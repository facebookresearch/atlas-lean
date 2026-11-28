/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRAL FLOW WITH MULTIPLIERS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND33] INTEGRAL FLOW WITH
MULTIPLIERS;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegralFlowWithMultipliers

/-- An instance: the vertex count `n`, the vertices `s` and `t`, the arcs
`(tail, head, capacity)`, the multipliers `h` (one per vertex), and the requirement `R`. -/
abbrev IntegralFlowWithMultipliersInstance :=
  ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ) × List ℕ × ℕ

/-- Well-formedness of an instance: `s` and `t` are distinct vertices; arcs join distinct
vertices below `n`, have positive capacities, and have distinct `(tail, head)` pairs; there is
one multiplier per vertex, positive at every `v ∉ {s, t}`; and `0 < R`. -/
def WellFormed (i : IntegralFlowWithMultipliersInstance) : Prop :=
  i.2.1 < i.1 ∧ i.2.2.1 < i.1 ∧ i.2.1 ≠ i.2.2.1 ∧
    (∀ a ∈ i.2.2.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1 ∧ 0 < a.2.2) ∧
    (i.2.2.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    i.2.2.2.2.1.length = i.1 ∧
    (∀ v < i.1, v ≠ i.2.1 → v ≠ i.2.2.1 → 0 < i.2.2.2.2.1.getD v 0) ∧
    0 < i.2.2.2.2.2

/-- The flow `f` on the arcs entering `v` (`f` is indexed by arc position). -/
def inflow (i : IntegralFlowWithMultipliersInstance) (f : ℕ → ℕ) (v : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range i.2.2.2.1.length).filter
    (fun k => (i.2.2.2.1.getD k (0, 0, 0)).2.1 = v), f k

/-- The flow `f` on the arcs leaving `v`. -/
def outflow (i : IntegralFlowWithMultipliersInstance) (f : ℕ → ℕ) (v : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range i.2.2.2.1.length).filter
    (fun k => (i.2.2.2.1.getD k (0, 0, 0)).1 = v), f k

/-- A flow within the capacities, with `h(v) * inflow = outflow` at every `v ∉ {s, t}`, whose
net flow into `t` is at least `R`. -/
def IntegralFlowWithMultipliersFeasible (i : IntegralFlowWithMultipliersInstance) : Prop :=
  ∃ f : ℕ → ℕ, (∀ k < i.2.2.2.1.length, f k ≤ (i.2.2.2.1.getD k (0, 0, 0)).2.2) ∧
    (∀ v < i.1, v ≠ i.2.1 → v ≠ i.2.2.1 →
      i.2.2.2.2.1.getD v 0 * inflow i f v = outflow i f v) ∧
    (i.2.2.2.2.2 : ℤ) ≤ (inflow i f i.2.2.1 : ℤ) - outflow i f i.2.2.1

open Classical in
/-- INTEGRAL FLOW WITH MULTIPLIERS as a decision problem over bitstrings. -/
noncomputable def integralFlowWithMultipliersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegralFlowWithMultipliersInstance) x with
  | some i => decide (WellFormed i ∧ IntegralFlowWithMultipliersFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegralFlowWithMultipliers
