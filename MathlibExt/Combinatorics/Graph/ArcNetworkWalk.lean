/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import MathlibExt.GameTheory.SelfishRouting

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# Arc walks and multiplicity edge volumes

Supplied routes as arc lists over a finite arc network `tail head : E → V`, their
traversal-count edge volumes, and node balance against the signed incidence matrix of
`MathlibExt.Combinatorics.Graph.ArcNetwork` (inflow minus outflow).

- W1 defines route validity (`IsArcWalk`: a directed walk as an arc list, arcs and nodes
  may repeat, parallel arcs told apart by identity) and the edge volume
  `edgeVolume edges f e = ∑ p, f p * (edges p).count e`, where a route traversing an arc
  twice loads it twice.
- W2 proves the route boundary identity and the route-by-route node balance of edge
  volumes, in the inflow-minus-outflow sign of `incidenceMatrix`.
- W3 reconciles this representation with the set-based routing model of
  `MathlibExt.GameTheory.SelfishRouting`: on routes that repeat no arc, its `edgeFlow`
  equals `edgeVolume`. A route with a repeated arc is outside the bridge and is never
  collapsed to a set of arcs.

Representation decision: the route representation of this module is the arc list with
`List.count` multiplicity. The vertex-pair path loads of
`MathlibExt.Probability.CanonicalPaths` are the analogous construction for canonical
paths between states; they are a different representation and are not reused here.

No link costs, equilibria, capacities or algorithms are stated. The demand-side
consequences (OD balance and admission) live in the consumer module
`PhyslibExt.FluidDynamics.Traffic.AssignmentBridge`.
-/

/-- Route validity: the arc list `l` is a directed walk from `o` to `d` in the network
`tail head : E → V`. The list is empty only when `o = d`; otherwise its first arc leaves `o`,
the head of each arc is the tail of the next, and its last arc enters `d`. Arcs and nodes may
repeat, and parallel arcs are told apart by identity. -/
def IsArcWalk {V E : Type*} (tail head : E → V) (o d : V) (l : List E) : Prop :=
  (l = [] → o = d) ∧ (∀ e ∈ l.head?, tail e = o) ∧
    l.IsChain (fun a b => head a = tail b) ∧ ∀ e ∈ l.getLast?, head e = d

/-- Edge volume of the path flow `f` on the supplied routes `edges`: every traversal counts,
`edgeVolume edges f e = ∑ p, f p * (edges p).count e`, in the flow unit of `f`. The
vertex-pair analogue for canonical paths between states is
`MathlibExt.Probability.CanonicalPaths.pathLoad`; here arcs are told apart by identity
and every traversal counts. -/
def edgeVolume {P E : Type*} [Fintype P] [DecidableEq E] (edges : P → List E) (f : P → ℝ)
    (e : E) : ℝ :=
  ∑ p, f p * ((edges p).count e : ℝ)

private lemma count_cons_add {E : Type*} [DecidableEq E] (a : E) (l : List E) (e : E) :
    ((List.count e (a :: l) : ℕ) : ℝ) =
      (List.count e l : ℝ) + (if e = a then (1 : ℝ) else 0) := by
  by_cases h : e = a
  · subst h
    rw [List.count_cons_self]
    push_cast
    rw [ite_eq_left rfl]
  · rw [List.count_cons_of_ne (Ne.symm h), ite_eq_right h, add_zero]

/-- The first arc of a nonempty valid walk leaves the origin. -/
lemma arcWalk_tail_head {V E : Type*} {tail head : E → V} {o d : V} {a : E}
    {l : List E} (h : IsArcWalk tail head o d (a :: l)) : tail a = o :=
  h.2.1 a (by simp)

/-- The only arc of a one-arc valid walk enters the destination. -/
lemma arcWalk_single_head {V E : Type*} {tail head : E → V} {o d : V} {a : E}
    (h : IsArcWalk tail head o d [a]) : head a = d :=
  h.2.2.2 a (by simp)

/-- Dropping the first arc of a valid walk with at least two arcs leaves a valid
walk from the head of the dropped arc. -/
lemma arcWalk_tail_of_cons {V E : Type*} {tail head : E → V} {o d : V} {a b : E}
    {l : List E} (h : IsArcWalk tail head o d (a :: b :: l)) :
    IsArcWalk tail head (head a) d (b :: l) := by
  have hchain := List.isChain_cons.mp h.2.2.1
  have hget : (a :: b :: l).getLast? = (b :: l).getLast? := List.getLast?_cons_cons
  refine ⟨?_, ?_, hchain.2, ?_⟩
  · intro hcon
    simp at hcon
  · intro e he
    rw [List.head?_cons] at he
    have heq : e = b := (Option.mem_some.mp he).symm
    rw [heq]
    exact (hchain.1 b (by simp)).symm
  · intro e he
    have he' : e ∈ (a :: b :: l).getLast? := by
      rw [hget]
      exact he
    exact h.2.2.2 e he'

private lemma arcWalk_boundary_aux {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] {tail head : E → V} (l : List E) :
    ∀ (o d : V),
      IsArcWalk tail head o d l →
        ∀ (v : V),
          (incidenceMatrix tail head).mulVec (fun e => (l.count e : ℝ)) v =
            (if d = v then 1 else 0) - (if o = v then 1 else 0) := by
  induction l with
  | nil =>
      intro o d hl v
      have hod : o = d := hl.1 rfl
      subst hod
      simp only [Matrix.mulVec, dotProduct, incidenceMatrix, List.count_nil, Nat.cast_zero,
        mul_zero, Finset.sum_const_zero, sub_self]
  | cons a l' ih =>
      intro o d hl v
      cases l' with
      | nil =>
          have htail : tail a = o := arcWalk_tail_head hl
          have hhead : head a = d := arcWalk_single_head hl
          subst htail
          subst hhead
          simp only [Matrix.mulVec, dotProduct, incidenceMatrix]
          simp_rw [count_cons_add a []]
          simp only [List.count_nil, Nat.cast_zero, zero_add]
          rw [Finset.sum_eq_single a
            (fun e _ hne => by rw [ite_eq_right hne, mul_zero])
            (fun hcon => absurd (Finset.mem_univ a) hcon)]
          simp [mul_one]
      | cons b l'' =>
          have htail : tail a = o := arcWalk_tail_head hl
          have hwalk' : IsArcWalk tail head (head a) d (b :: l'') :=
            arcWalk_tail_of_cons hl
          have ih' := ih (head a) d hwalk' v
          simp only [Matrix.mulVec, dotProduct, incidenceMatrix]
          simp_rw [count_cons_add a (b :: l''), mul_add, Finset.sum_add_distrib]
          have hsing : (∑ e,
                (((if head e = v then (1 : ℝ) else 0) - (if tail e = v then 1 else 0)) *
                  (if e = a then (1 : ℝ) else 0))) =
              ((if head a = v then (1 : ℝ) else 0) - (if tail a = v then 1 else 0)) := by
            rw [Finset.sum_eq_single a
              (fun e _ hne => by rw [ite_eq_right hne, mul_zero])
              (fun hcon => absurd (Finset.mem_univ a) hcon)]
            simp [mul_one]
          rw [hsing]
          have hfirst : (∑ e,
                (((if head e = v then (1 : ℝ) else 0) - (if tail e = v then 1 else 0)) *
                  ((List.count e (b :: l'') : ℕ) : ℝ))) =
              (if d = v then (1 : ℝ) else 0) - (if head a = v then 1 else 0) := by
            simpa [Matrix.mulVec, dotProduct, incidenceMatrix] using ih'
          rw [hfirst, htail]
          ring

/-- Nonnegative path flows give nonnegative edge volumes: each term is a nonnegative flow
times a traversal count. -/
theorem edgeVolume_nonneg {P E : Type*} [Fintype P] [DecidableEq E] (edges : P → List E)
    {f : P → ℝ} (hf : ∀ p, 0 ≤ f p) (e : E) : 0 ≤ edgeVolume edges f e := by
  unfold edgeVolume
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hf p) (Nat.cast_nonneg _)

/-- Route boundary identity, inflow minus outflow: the traversal-count vector of a valid walk
`l` from `o` to `d` has node balance `1[d = v] - 1[o = v]` at every node `v`. Interior visits,
repeated arcs and loops cancel; an empty or closed walk (`o = d`) has zero balance. -/
theorem IsArcWalk.incidenceMatrix_mulVec_count {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {tail head : E → V} {o d : V} {l : List E}
    (hl : IsArcWalk tail head o d l) (v : V) :
    (incidenceMatrix tail head).mulVec (fun e => (l.count e : ℝ)) v =
      (if d = v then 1 else 0) - (if o = v then 1 else 0) := by
  exact arcWalk_boundary_aux l o d hl v

/-- Node balance of the edge volumes, route by route: if every supplied route is a valid walk
from its origin to its destination, inflow minus outflow of the edge volumes at `v` is the
flow on routes ending at `v` minus the flow on routes starting at `v`. No sign or demand
condition on `f` is used. The per-route identity is the arc-list form of the telescoping
`MathlibExt.Probability.CanonicalPaths.sum_pathEdges_sub`. -/
theorem incidenceMatrix_mulVec_edgeVolume {V E P : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype P] {tail head : E → V} {orig dest : P → V}
    {edges : P → List E} (hwalk : ∀ p, IsArcWalk tail head (orig p) (dest p) (edges p))
    (f : P → ℝ) (v : V) :
    (incidenceMatrix tail head).mulVec (edgeVolume edges f) v =
      ∑ p, f p * ((if dest p = v then 1 else 0) - (if orig p = v then 1 else 0)) := by
  have h2 : ∀ p, (∑ e,
        (((if head e = v then (1 : ℝ) else 0) - (if tail e = v then 1 else 0)) *
          ((List.count e (edges p) : ℕ) : ℝ))) =
        (if dest p = v then (1 : ℝ) else 0) - (if orig p = v then 1 else 0) := by
    intro p
    simpa [Matrix.mulVec, dotProduct, incidenceMatrix] using
      (IsArcWalk.incidenceMatrix_mulVec_count (hwalk p) v)
  simp only [Matrix.mulVec, dotProduct, incidenceMatrix, edgeVolume]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hfac : (∑ e,
        (((if head e = v then (1 : ℝ) else 0) - (if tail e = v then 1 else 0)) *
          (f p * ((List.count e (edges p) : ℕ) : ℝ)))) =
        f p * (∑ e,
          (((if head e = v then (1 : ℝ) else 0) - (if tail e = v then 1 else 0)) *
            ((List.count e (edges p) : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hfac, h2 p]

/-- Link-simple bridge to the set-based routing model: on the OD instance with commodity
`p ↦ (orig p, dest p)`, arc sets `(edges p).toFinset` and any latency `ℓ`, routes that repeat
no arc give `edgeFlow f e = edgeVolume edges f e`. Neither side depends on the commodity or
the latency. `Nodup` is needed: `edgeFlow` counts a repeated arc once. -/
theorem edgeFlow_eq_edgeVolume {V E P : Type*} [Fintype P] [DecidableEq E]
    (orig dest : P → V) (edges : P → List E) (ℓ : E → ℝ → ℝ)
    (hsimple : ∀ p, (edges p).Nodup) (f : P → ℝ) (e : E) :
    MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow
        { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset,
          latency := ℓ } f e =
      edgeVolume edges f e := by
  simp only [MathlibExt.GameTheory.SelfishRouting.RoutingInstance.edgeFlow, edgeVolume]
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

end MathlibExt.Combinatorics.Graph.ArcNetwork
