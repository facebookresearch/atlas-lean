/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.EdmondsKarp
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Edmonds-Karp computes a maximum flow and a minimum cut

The algorithmic side of the max-flow min-cut theorem. MathlibExt's
`MathlibExt/Combinatorics/Graph/MaxFlowMinCut.lean` proves the theorem for real capacity matrices
by compactness (`max_flow_min_cut`: a maximum flow exists and equals a minimum cut capacity), and
`MathlibExt/Combinatorics/Graph/IntegralFlow.lean` proves integrality the same way. This module
connects the executable Edmonds-Karp algorithm (`Graph/EdmondsKarp.lean`, integral capacities on
`Fin n`, skew-symmetric integer flows) to MathlibExt's definitions `IsFeasibleFlow`, `flowValue`,
`IsSTCut` and `cutCapacity`, so the maximum flow, the minimum cut and the integral optimum are
computed rather than shown to exist.

Main results:

* `realCap`, `arcFlow`, `realFlow`: capacities and flows in MathlibExt's real, nonnegative arc
  representation (a skew flow's positive part, `flow_eq_arcFlow_sub`);
  `isFeasibleFlow_realFlow`, `flowValue_realFlow`, `cutCapacity_realCap`: feasibility, flow
  value and cut capacity agree across the representations.
* `edmondsKarp_max_flow_min_cut`: **`edmondsKarp` computes a maximum flow**, in the shape of
  MathlibExt's `max_flow_min_cut`: feasible, at least every feasible real flow, at most every
  cut, and equal to the capacity of its certificate cut `residualCut` (`isSTCut_residualCut`);
  `cutCapacity_residualCut_le`: that cut is a minimum cut.
* `exists_nat_max_flow`: **integral capacities have an integral maximum flow**, natural-valued
  on every arc, given by `edmondsKarp`.

Related: the Bertsimas-Tsitsiklis blueprint (`FormalizedTextbooks/BertsimasLinearOptimization`,
chapter 7, maximum flow) plans Ford-Fulkerson termination and Theorem 7.10 with no Lean yet.

## Cost model

No new cost claim; `Graph/EdmondsKarp.lean` documents the algorithm's implementation-level cost.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Graph.MaxFlowMinCut

open Cslib.Algorithms.Lean.EdmondsKarp
open DirectedAdjacency BreadthFirstSearch
open scoped BigOperators

local notation "MFC.IsFeasibleFlow" =>
  MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
local notation "MFC.flowValue" =>
  MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue
local notation "MFC.IsSTCut" =>
  MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsSTCut
local notation "MFC.cutCapacity" =>
  MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.cutCapacity

variable {n : ℕ}

/-- The capacities as reals. -/
def realCap (capacity : Fin n → Fin n → ℕ) : Fin n → Fin n → ℝ := fun u v => (capacity u v : ℝ)

/-- A skew-symmetric flow as a nonnegative arc flow: its positive part, as naturals. -/
def arcFlow (flow : Flow n) : Fin n → Fin n → ℕ := fun u v => (flow u v).toNat

/-- The arc flow as reals. -/
def realFlow (flow : Flow n) : Fin n → Fin n → ℝ := fun u v => (arcFlow flow u v : ℝ)

/-- A skew-symmetric flow is the difference of its arc flow in the two directions. -/
theorem flow_eq_arcFlow_sub {flow : Flow n} (skew : ∀ u v, flow u v = -flow v u) (u v : Fin n) :
    flow u v = (arcFlow flow u v : ℤ) - (arcFlow flow v u : ℤ) := by
  simp only [arcFlow, skew v u]
  omega

theorem realFlow_sub {flow : Flow n} (skew : ∀ u v, flow u v = -flow v u) (u v : Fin n) :
    realFlow flow u v - realFlow flow v u = (flow u v : ℝ) := by
  rw [flow_eq_arcFlow_sub skew u v]
  simp only [realFlow, Int.cast_sub, Int.cast_natCast]

/-- The net outflow of `v` in the skew representation is its outflow minus its inflow in the arc
representation. -/
theorem sum_realFlow_sub {flow : Flow n} (skew : ∀ u v, flow u v = -flow v u) (v : Fin n) :
    (∑ w, realFlow flow v w) - ∑ u, realFlow flow u v = (EdmondsKarp.flowValue v flow : ℝ) := by
  rw [← Finset.sum_sub_distrib, EdmondsKarp.flowValue, Int.cast_sum]
  exact Finset.sum_congr rfl fun w _ => realFlow_sub skew v w

/-- **A feasible skew flow gives a feasible flow** in MathlibExt's sense, with the same value. -/
theorem isFeasibleFlow_realFlow {capacity : Fin n → Fin n → ℕ} {source sink : Fin n}
    {flow : Flow n} (h : IsFeasible capacity source sink flow) :
    MFC.IsFeasibleFlow (realCap capacity) source sink (realFlow flow) := by
  obtain ⟨skew, cap, cons⟩ := h
  refine ⟨fun u v => by simp [realFlow], fun u v => ?_, fun v hs ht => ?_⟩
  · have := cap u v
    simp only [realFlow, realCap, arcFlow]
    exact_mod_cast (by omega : (flow u v).toNat ≤ capacity u v)
  · have := sum_realFlow_sub skew v
    rw [cons v hs ht] at this
    push_cast at this
    linarith

theorem flowValue_realFlow {flow : Flow n} (skew : ∀ u v, flow u v = -flow v u) (s : Fin n) :
    MFC.flowValue s (realFlow flow) = (EdmondsKarp.flowValue s flow : ℝ) :=
  sum_realFlow_sub skew s

theorem cutCapacity_realCap (capacity : Fin n → Fin n → ℕ) (S : Finset (Fin n)) :
    MFC.cutCapacity (realCap capacity) S = (EdmondsKarp.cutCapacity capacity S : ℝ) := by
  simp only [MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.cutCapacity,
    EdmondsKarp.cutCapacity, realCap, Int.cast_sum, Int.cast_natCast]

/-- The certificate cut of the Edmonds-Karp flow separates the source from the sink. -/
theorem isSTCut_residualCut (capacity : Fin n → Fin n → ℕ) {source sink : Fin n}
    (hst : source ≠ sink) :
    MFC.IsSTCut source sink (residualCut capacity (edmondsKarp capacity source sink) source) := by
  refine ⟨?_, ?_⟩
  · simp only [residualCut, List.mem_toFinset]
    rw [order_mem_iff_reachable]
    exact Relation.ReflTransGen.refl
  · simp only [residualCut, List.mem_toFinset]
    rw [order_mem_iff_reachable]
    exact edmondsKarp_no_augmenting_path capacity hst

/-- **Edmonds-Karp computes a maximum flow and a minimum cut**, in the statement shape of
MathlibExt's `max_flow_min_cut`: for integral capacities on `Fin n` and `source ≠ sink`, the arc
flow of `edmondsKarp` (`realFlow`) is feasible, no feasible real flow has a larger value, its value
is at most every cut's capacity, and it equals the capacity of the certificate cut
`residualCut`. -/
theorem edmondsKarp_max_flow_min_cut (capacity : Fin n → Fin n → ℕ) {source sink : Fin n}
    (hst : source ≠ sink) :
    MFC.IsFeasibleFlow (realCap capacity) source sink
        (realFlow (edmondsKarp capacity source sink)) ∧
      (∀ f : Fin n → Fin n → ℝ, MFC.IsFeasibleFlow (realCap capacity) source sink f →
        MFC.flowValue source f ≤
          MFC.flowValue source (realFlow (edmondsKarp capacity source sink))) ∧
      (∀ S : Finset (Fin n), MFC.IsSTCut source sink S →
        MFC.flowValue source (realFlow (edmondsKarp capacity source sink)) ≤
          MFC.cutCapacity (realCap capacity) S) ∧
      MFC.IsSTCut source sink (residualCut capacity (edmondsKarp capacity source sink) source) ∧
      MFC.flowValue source (realFlow (edmondsKarp capacity source sink)) =
        MFC.cutCapacity (realCap capacity)
          (residualCut capacity (edmondsKarp capacity source sink) source) := by
  have hfeas := edmondsKarp_feasible capacity source sink
  have hF := isFeasibleFlow_realFlow hfeas
  have hcut := isSTCut_residualCut capacity hst
  have heq : MFC.flowValue source (realFlow (edmondsKarp capacity source sink)) =
      MFC.cutCapacity (realCap capacity)
        (residualCut capacity (edmondsKarp capacity source sink) source) := by
    rw [flowValue_realFlow hfeas.1, cutCapacity_realCap, edmondsKarp_minCut capacity hst]
  refine ⟨hF, fun f hf => ?_, fun S hS => ?_, hcut, heq⟩
  · rw [heq]
    exact MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue_le_cutCapacity _ _ _ f hf
      _ hcut
  · exact MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue_le_cutCapacity _ _ _ _ hF
      S hS

/-- The certificate cut is a minimum cut: no `s`-`t` cut has smaller capacity. -/
theorem cutCapacity_residualCut_le (capacity : Fin n → Fin n → ℕ) {source sink : Fin n}
    (hst : source ≠ sink) {S : Finset (Fin n)} (hS : MFC.IsSTCut source sink S) :
    MFC.cutCapacity (realCap capacity)
        (residualCut capacity (edmondsKarp capacity source sink) source) ≤
      MFC.cutCapacity (realCap capacity) S := by
  obtain ⟨-, -, hle, -, heq⟩ := edmondsKarp_max_flow_min_cut capacity hst
  rw [← heq]
  exact hle S hS

/-- **Integrality**: integral capacities have an integral maximum flow, computed by
`edmondsKarp` (`arcFlow`, natural-valued on every arc), as a real flow in MathlibExt's sense. -/
theorem exists_nat_max_flow (capacity : Fin n → Fin n → ℕ) {source sink : Fin n}
    (hst : source ≠ sink) :
    ∃ f : Fin n → Fin n → ℕ,
      MFC.IsFeasibleFlow (realCap capacity) source sink (fun u v => (f u v : ℝ)) ∧
      ∀ g : Fin n → Fin n → ℝ, MFC.IsFeasibleFlow (realCap capacity) source sink g →
        MFC.flowValue source g ≤ MFC.flowValue source (fun u v => (f u v : ℝ)) := by
  obtain ⟨hF, hmax, -⟩ := edmondsKarp_max_flow_min_cut capacity hst
  exact ⟨arcFlow (edmondsKarp capacity source sink), hF, hmax⟩

end Cslib.Algorithms.Lean.Graph.MaxFlowMinCut
