/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.SelfishRoutingArcWalkBridge
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Arc-walk bridge checks

Concrete consumers of `MathlibExt.GameTheory.SelfishRoutingArcWalkBridge`: the
arc-simple bridge instance with both sides `![1, 2, 3, 0]`, and the non-simple
counterexample (`edgeFlow` 4 against `edgeVolume` 7 on arc 0).

These are elaboration and non-vacuity checks, not new results.
-/

open MathlibExt.Combinatorics.Graph.ArcNetwork
open Matrix

/-- Bridge instance: on the arc-simple routes `[0, 2]`, `[1, 2]` with flows `1`, `2`,
the set-based `edgeFlow` and the multiplicity `edgeVolume` both equal `![1, 2, 3, 0]`
(the parallel arcs `0` and `1` stay distinct, arc `2` is shared). -/
example :
    edgeVolume ![([0, 2] : List (Fin 4)), [1, 2]] ![1, 2] = ![1, 2, 3, 0] ∧
      (fun e => MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow
        { commodity := fun _ : Fin 2 => ((0 : Fin 3), (2 : Fin 3)),
          edges := fun p => (![([0, 2] : List (Fin 4)), [1, 2]] p).toFinset,
          latency := fun _ _ => 0 } ![1, 2] e) = ![1, 2, 3, 0] := by
  constructor
  · funext e
    fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num
  · funext e
    rw [
      MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow_eq_edgeVolume
        (fun _ => 0) (fun _ => 2)
      ![([0, 2] : List (Fin 4)), [1, 2]] (fun _ _ => 0)
      (fun p => by fin_cases p <;> decide) ![1, 2] e]
    fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num

/-- Non-simple counterexample: the route `[0, 2, 3, 0, 2]` traverses arc `0` twice, so
with flows `3` on it and `1` on `[0, 2]`, arc `0` has `edgeVolume` `7` but set-based
`edgeFlow` `4`; the bridge does not apply. -/
example :
    edgeVolume ![([0, 2, 3, 0, 2] : List (Fin 4)), [0, 2]] ![3, 1] 0 = 7 ∧
      MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow
          { commodity := fun _ : Fin 2 => ((0 : Fin 3), (2 : Fin 3)),
            edges := fun p => (![([0, 2, 3, 0, 2] : List (Fin 4)), [0, 2]] p).toFinset,
            latency := fun _ _ => 0 } ![3, 1] 0 = 4 ∧
      ¬ ([0, 2, 3, 0, 2] : List (Fin 4)).Nodup := by
  refine ⟨?_, ?_, by decide⟩
  · simp [edgeVolume, Fin.sum_univ_two] <;> norm_num
  · simp [MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow, Finset.sum_filter,
      Fin.sum_univ_two] <;> norm_num

open MathlibExt.GameTheory.SelfishRouting

/-! ### Travel-time bridge checks -/

/-- Link travel times with distinct slopes per arc: `t e x = (e + 1) x + 1`. -/
private noncomputable def tt (e : Fin 4) (x : ℝ) : ℝ := (((e : ℕ) : ℝ) + 1) * x + 1

/-- Two routes sharing arc `2`; the parallel arcs `0` and `1` stay distinct. -/
private abbrev sharedRoutes : Fin 2 → List (Fin 4) := ![[0, 2], [1, 2]]
/-- Route `0` traverses arcs `0` and `2` twice. -/
private abbrev doubleRoutes : Fin 2 → List (Fin 4) := ![[0, 2, 3, 0, 2], [0, 2]]
/-- `sharedRoutes` plus the route `[0, 2, 3, 0, 2]`, which will carry zero flow. -/
private abbrev zeroFlowRoutes : Fin 3 → List (Fin 4) := ![[0, 2], [1, 2], [0, 2, 3, 0, 2]]

private theorem sharedArcVolume : edgeVolume sharedRoutes ![1, 2] = ![1, 2, 3, 0] := by
  funext e
  fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num

example : (fun e => tt e (edgeVolume sharedRoutes ![1, 2] e)) = ![2, 5, 10, 1] := by
  rw [sharedArcVolume]
  funext e
  fin_cases e <;> simp [tt] <;> norm_num

private theorem doubleTraversalVolume : edgeVolume doubleRoutes ![3, 1] = ![7, 0, 7, 3] := by
  funext e
  fin_cases e <;> simp [edgeVolume, Fin.sum_univ_two] <;> norm_num

/-- The toFinset OD instance of `doubleRoutes` with latency `tt`. -/
private noncomputable abbrev doubleRouteInstance : RoutingInstance (Fin 4) (Fin 3 × Fin 3) (Fin 2) :=
  { commodity := fun _ => ((0 : Fin 3), (2 : Fin 3)), edges := fun p => (doubleRoutes p).toFinset,
    latency := tt }

private theorem doubleTraversalEdgeFlow (e : Fin 4) : doubleRouteInstance.edgeFlow ![3, 1] e = ![4, 0, 4, 3] e := by
  fin_cases e <;> simp [RoutingInstance.edgeFlow, Finset.sum_filter, Fin.sum_univ_two] <;>
    norm_num

/-- The canonical set-based cost on the same routes is 111, not 249. -/
example : doubleRouteInstance.cost ![3, 1] = 111 := by
  simp only [RoutingInstance.cost, doubleTraversalEdgeFlow, Fin.sum_univ_four]
  simp [tt]
  norm_num

/-! ### T2: bridge instance, counterexamples, premise equivalence, composition -/

example {V E P : Type*} [Fintype P] [DecidableEq E] (orig dest : P → V) (edges : P → List E)
    (ℓ : E → ℝ → ℝ) (hsimple : ∀ p, (edges p).Nodup) (f : P → ℝ) (p : P) :
    RoutingInstance.pathLatency
        { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset,
          latency := ℓ } f p =
      ((edges p).map fun e => ℓ e (edgeVolume edges f e)).sum :=
  RoutingInstance.pathLatency_eq_sum_map orig dest edges ℓ hsimple f p

/-- The OD commodity is no restriction: `pathLatency` ignores the commodity, so the statement at
any commodity map follows by unfolding (here from the `Unit` OD instance). -/
example {ι E P : Type*} [Fintype P] [DecidableEq E] (c : P → ι) (edges : P → List E)
    (ℓ : E → ℝ → ℝ) (hsimple : ∀ p, (edges p).Nodup) (f : P → ℝ) (p : P) :
    RoutingInstance.pathLatency
        { commodity := c, edges := fun p => (edges p).toFinset, latency := ℓ } f p =
      ((edges p).map fun e => ℓ e (edgeVolume edges f e)).sum :=
  RoutingInstance.pathLatency_eq_sum_map (V := Unit) (fun _ => ()) (fun _ => ()) edges ℓ hsimple f p

/-- On the arc-simple routes `sharedRoutes`, `pathLatency` is the route time (12 and 15). -/
example : RoutingInstance.pathLatency
      { commodity := fun _ => ((0 : Fin 3), (2 : Fin 3)), edges := fun p => (sharedRoutes p).toFinset,
        latency := tt } ![1, 2] 0 = 12 ∧
    RoutingInstance.pathLatency
      { commodity := fun _ => ((0 : Fin 3), (2 : Fin 3)), edges := fun p => (sharedRoutes p).toFinset,
        latency := tt } ![1, 2] 1 = 15 := by
  have hs : ∀ p, (sharedRoutes p).Nodup := fun p => by fin_cases p <;> decide
  rw [RoutingInstance.pathLatency_eq_sum_map (fun _ => 0) (fun _ => 2) sharedRoutes tt hs,
    RoutingInstance.pathLatency_eq_sum_map (fun _ => 0) (fun _ => 2) sharedRoutes tt hs, sharedArcVolume]
  constructor
  · simp [tt]
    norm_num
  · simp [tt]
    norm_num

/-- Route `[0, 2, 3, 0, 2]` repeats arcs; set-based `pathLatency` 31 against route time 73. -/
example : RoutingInstance.pathLatency
      { commodity := fun _ => ((0 : Fin 3), (2 : Fin 3)), edges := fun p => (doubleRoutes p).toFinset,
        latency := tt } ![3, 1] 0 = 31 ∧
    ((doubleRoutes 0).map fun e => tt e (edgeVolume doubleRoutes ![3, 1] e)).sum = 73 := by
  constructor
  · have hfs : (doubleRoutes 0).toFinset = {0, 2, 3} := by decide
    simp only [RoutingInstance.pathLatency, hfs]
    simp [RoutingInstance.edgeFlow, Finset.sum_filter, Fin.sum_univ_two, tt]
    norm_num
  · rw [doubleTraversalVolume]
    simp [tt]
    norm_num

/-- Route `[0]` repeats no arc, but route `[0, 0]` repeats the arc it shares: at route `0`
`pathLatency` is 2 and the route time 3. `Nodup` is needed for every route, not only `p`. -/
example : RoutingInstance.pathLatency
      { commodity := fun _ => ((0 : Fin 3), (2 : Fin 3)),
        edges := fun p => ((![[0], [0, 0]] : Fin 2 → List (Fin 4)) p).toFinset,
        latency := fun _ x => x } ![1, 1] 0 = 2 ∧
    (((![[0], [0, 0]] : Fin 2 → List (Fin 4)) 0).map fun e =>
      edgeVolume (![[0], [0, 0]] : Fin 2 → List (Fin 4)) ![1, 1] e).sum = 3 := by
  constructor
  · simp [RoutingInstance.pathLatency, RoutingInstance.edgeFlow, Finset.sum_filter,
      Fin.sum_univ_two]
    norm_num
  · simp [edgeVolume, Fin.sum_univ_two]
    norm_num

/-- Premise equivalence: if the conclusion holds for every latency, flow and route, every route
repeats no arc (take constant latency `1`). With T2, `hsimple` is exactly that condition. -/
example {V E P : Type*} [Fintype P] [DecidableEq E] (orig dest : P → V) (edges : P → List E)
    (h : ∀ (ℓ : E → ℝ → ℝ) (f : P → ℝ) (p : P), RoutingInstance.pathLatency
        { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset,
          latency := ℓ } f p = ((edges p).map fun e => ℓ e (edgeVolume edges f e)).sum) :
    ∀ p, (edges p).Nodup := by
  intro p
  have h1 := h (fun _ _ => 1) 0 p
  simp only [RoutingInstance.pathLatency, Finset.sum_const, nsmul_eq_mul, mul_one,
    List.map_const', List.sum_replicate] at h1
  have h2 : (edges p).toFinset.card = (edges p).length := by exact_mod_cast h1
  rw [List.card_toFinset] at h2
  exact List.dedup_eq_self.mp ((List.dedup_sublist _).eq_of_length h2)

/-- Composition with the canonical cost (owner `cost_eq_sum_pathLatency_mul`): on link-simple
routes the set-based cost is the edge-side total travel time. The owner orders factors latency
first, so `mul_comm` is needed. -/
example {V E P : Type*} [Fintype P] [Fintype E] [DecidableEq E] (orig dest : P → V)
    (edges : P → List E) (ℓ : E → ℝ → ℝ) (hsimple : ∀ p, (edges p).Nodup) (f : P → ℝ) :
    RoutingInstance.cost
        { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset,
          latency := ℓ } f =
      ∑ e, edgeVolume edges f e * ℓ e (edgeVolume edges f e) := by
  rw [RoutingInstance.cost_eq_sum_pathLatency_mul, ← sum_mul_sum_map_eq_sum_edgeVolume_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [RoutingInstance.pathLatency_eq_sum_map orig dest edges ℓ hsimple f p, mul_comm]


#print axioms MathlibExt.GameTheory.SelfishRouting.RoutingInstance.pathLatency_eq_sum_map
