/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH CONSTRAINED NETWORK FLOW: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND34] PATH CONSTRAINED NETWORK FLOW
(p. 215; credited there to H. J. Prömel, 1978; transformation from 3SAT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut
public import CSLibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), the arcs
`(tail, head, capacity)`, `s`, `t`, the collection `P` of paths (vertex lists), and the
requirement `R`. -/
abbrev PathConstrainedNetworkFlowInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × List (List ℕ) × ℕ

/-- The arcs `(u, v)` of the arc records. -/
def arcs (i : PathConstrainedNetworkFlowInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun a => (a.1, a.2.1)

/-- The capacity `c(u, v)` of the arc from `u` to `v`, and `0` when there is no such arc. -/
def capacity (i : PathConstrainedNetworkFlowInstance) (u v : ℕ) : ℕ :=
  ((i.2.1.find? fun a => a.1 = u ∧ a.2.1 = v).map fun a => a.2.2).getD 0

/-- The flow on `(u, v)` induced by `g` (indexed by position in `P`): the sum of `g` over the
paths of `P` that contain the arc `(u, v)`, i.e. `∑_{p ∈ P(u, v)} g(p)`. -/
def pathFlow {α : Type*} [AddCommMonoid α] (i : PathConstrainedNetworkFlowInstance)
    (g : ℕ → α) (u v : ℕ) : α :=
  ∑ j ∈ (Finset.range i.2.2.2.2.1.length).filter
      (fun j => (u, v) ∈ (i.2.2.2.2.1.getD j []).zip (i.2.2.2.2.1.getD j []).tail), g j

/-- Well-formedness of an instance: the arc records describe a directed graph on
`0, ..., n - 1` (endpoints in range, no self-loops, no repeated arcs), every capacity is positive,
`s` and `t` are distinct vertices, every member of `P` is a directed path in `G` (its vertices
are in `V`, also when it has a single vertex), and `R` is positive. -/
def WellFormed (i : PathConstrainedNetworkFlowInstance) : Prop :=
  ((arcs i).Nodup ∧ ∀ a ∈ arcs i, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    (∀ a ∈ i.2.1, 0 < a.2.2) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧
    (∀ p ∈ i.2.2.2.2.1, (∀ v ∈ p, v < i.1) ∧
      ∃ a b, DirectedTwoDisjointConnectingPaths.IsDirectedPath (arcs i) a b p) ∧
    0 < i.2.2.2.2.2

/-- Some `g : P → ℤ₀⁺` induces a flow within the capacities, conserved at every vertex other than
`s` and `t`, with net flow into `t` at least `R`. -/
def PathConstrainedNetworkFlowFeasible (i : PathConstrainedNetworkFlowInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1), ∃ g : ℕ → ℕ,
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩
        (fun u v => ((pathFlow i g u v : ℕ) : ℝ)) ∧
      (i.2.2.2.2.2 : ℝ) ≤ (∑ u : Fin i.1, ((pathFlow i g u i.2.2.2.1 : ℕ) : ℝ)) -
        ∑ w : Fin i.1, ((pathFlow i g i.2.2.2.1 w : ℕ) : ℝ)

open Classical in
/-- PATH CONSTRAINED NETWORK FLOW as a decision problem over bitstrings. -/
noncomputable def pathConstrainedNetworkFlowDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathConstrainedNetworkFlowInstance) x with
  | some i => decide (WellFormed i ∧ PathConstrainedNetworkFlowFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow
