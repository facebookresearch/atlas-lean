/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SelfishRouting
public import MathlibExt.Combinatorics.Graph.ArcNetworkWalk

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.GameTheory.SelfishRouting.RoutingInstance

open MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# Bridge from arc lists to set-based routing

The set-based routing model of `MathlibExt.GameTheory.SelfishRouting` stores a route
as its arc set, and its `edgeFlow` counts a route once on each of its arcs. The
arc-list model of `MathlibExt.Combinatorics.Graph.ArcNetworkWalk` stores a route as
an arc list, and its `edgeVolume` counts every traversal. On routes that repeat no
arc the two counts agree (`edgeFlow_eq_edgeVolume`); a route with a repeated arc is
outside the bridge and is never collapsed to a set of arcs. On routes that repeat no
arc, `pathLatency` is also the arc-list route travel time at the induced volumes
(`pathLatency_eq_sum_map`).
-/

/-- Link-simple bridge to the set-based routing model: on the OD instance with commodity
`p ↦ (orig p, dest p)`, arc sets `(edges p).toFinset` and any latency `ℓ`, routes that repeat
no arc give `edgeFlow f e = edgeVolume edges f e`. Neither side depends on the commodity or
the latency. `Nodup` is needed: `edgeFlow` counts a repeated arc once. -/
theorem edgeFlow_eq_edgeVolume {V E P : Type*} [Fintype P] [DecidableEq E]
    (orig dest : P → V) (edges : P → List E) (ℓ : E → ℝ → ℝ)
    (hsimple : ∀ p, (edges p).Nodup) (f : P → ℝ) (e : E) :
    RoutingInstance.edgeFlow
        { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset,
          latency := ℓ } f e =
      edgeVolume edges f e := by
  simp only [RoutingInstance.edgeFlow, edgeVolume]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  have hnodup := hsimple p
  by_cases h : e ∈ edges p
  · rw [List.count_eq_one_of_mem hnodup h, ite_eq_left (List.mem_toFinset.mpr h)]
    simp
  · rw [List.count_eq_zero_of_not_mem h,
      ite_eq_right (fun hm => h (List.mem_toFinset.mp hm))]
    simp

/-- Link-simple bridge for route travel times: on the OD instance with commodity
`p ↦ (orig p, dest p)`, arc sets `(edges p).toFinset` and latency `ℓ`, routes that repeat no
arc give `pathLatency f p = ((edges p).map fun e => ℓ e (edgeVolume edges f e)).sum`, the route
travel time at the induced volumes. Neither side depends on the commodity. `Nodup` is needed:
`pathLatency` charges a repeated arc once, at the set-based `edgeFlow`. With
`cost_eq_sum_pathLatency_mul` and `sum_mul_sum_map_eq_sum_edgeVolume_mul`, the set-based cost
of such routes is the edge-side total travel time. -/
theorem pathLatency_eq_sum_map {V E P : Type*} [Fintype P] [DecidableEq E]
    (orig dest : P → V) (edges : P → List E) (ℓ : E → ℝ → ℝ)
    (hsimple : ∀ p, (edges p).Nodup) (f : P → ℝ) (p : P) :
    RoutingInstance.pathLatency
        { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset,
          latency := ℓ } f p =
      ((edges p).map fun e => ℓ e (edgeVolume edges f e)).sum := by
  have hsum : ((edges p).map fun e => ℓ e (edgeVolume edges f e)).sum
      = (edges p).toFinset.sum (fun e => ℓ e (edgeVolume edges f e)) :=
    (List.sum_toFinset _ (hsimple p)).symm
  rw [hsum]
  simp only [RoutingInstance.pathLatency]
  apply Finset.sum_congr rfl
  intro e _
  rw [edgeFlow_eq_edgeVolume orig dest edges ℓ hsimple f e]

end MathlibExt.GameTheory.SelfishRouting.RoutingInstance
