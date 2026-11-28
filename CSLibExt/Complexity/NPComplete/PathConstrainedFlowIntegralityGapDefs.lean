/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH CONSTRAINED NETWORK FLOW without an integrality gap: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND34] PATH CONSTRAINED NETWORK FLOW
(p. 215), comment "The corresponding problem with non-integral flows is equivalent to LINEAR
PROGRAMMING, but the question of whether the best rational flow fails to exceed the best integral
flow is NP-complete" (credited there to H. J. Prömel, 1978).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathConstrainedNetworkFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathConstrainedFlowIntegralityGap

open MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow
  (PathConstrainedNetworkFlowInstance capacity pathFlow)
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), the arcs
`(tail, head, capacity)`, `s`, `t`, and the collection `P` of paths (vertex lists). -/
abbrev PathConstrainedFlowIntegralityGapInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × List (List ℕ)

/-- The PATH CONSTRAINED NETWORK FLOW instance with the same network and paths and the
requirement `R = 1`, which nothing here reads. -/
def toParent (i : PathConstrainedFlowIntegralityGapInstance) :
    PathConstrainedNetworkFlowInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, 1)

/-- Well-formedness of an instance: the parent's for `toParent i`. -/
def WellFormed (i : PathConstrainedFlowIntegralityGapInstance) : Prop :=
  PathConstrainedNetworkFlow.WellFormed (toParent i)

/-- Some integral path flow is feasible and its net flow into `t` is at least that of every
feasible rational path flow (nonnegative rational amounts on the paths). -/
def NoIntegralityGapFeasible (i : PathConstrainedFlowIntegralityGapInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1), ∃ g : ℕ → ℕ,
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity (toParent i) u v : ℝ)) ⟨i.2.2.1, hs⟩
        ⟨i.2.2.2.1, ht⟩ (fun u v => ((pathFlow (toParent i) g u v : ℕ) : ℝ)) ∧
      ∀ q : ℕ → ℚ, (∀ j, 0 ≤ q j) →
        IsFeasibleFlow (fun u v : Fin i.1 => (capacity (toParent i) u v : ℝ)) ⟨i.2.2.1, hs⟩
            ⟨i.2.2.2.1, ht⟩ (fun u v => ((pathFlow (toParent i) q u v : ℚ) : ℝ)) →
          (∑ u : Fin i.1, ((pathFlow (toParent i) q u i.2.2.2.1 : ℚ) : ℝ)) -
              ∑ w : Fin i.1, ((pathFlow (toParent i) q i.2.2.2.1 w : ℚ) : ℝ) ≤
            (∑ u : Fin i.1, ((pathFlow (toParent i) g u i.2.2.2.1 : ℕ) : ℝ)) -
              ∑ w : Fin i.1, ((pathFlow (toParent i) g i.2.2.2.1 w : ℕ) : ℝ)

open Classical in
/-- PATH CONSTRAINED NETWORK FLOW without an integrality gap as a decision problem over
bitstrings. -/
noncomputable def pathConstrainedFlowIntegralityGapDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathConstrainedFlowIntegralityGapInstance) x with
  | some i => decide (WellFormed i ∧ NoIntegralityGapFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathConstrainedFlowIntegralityGap
