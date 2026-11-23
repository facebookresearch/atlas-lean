/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetwork

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
- W3 proves the travel-time pairing at fixed link costs: the flow-weighted sum of route
  travel times equals the edge-side total `∑ e, x e * t e (x e)`, with multiplicity on
  both sides (a route traversing an arc twice pays and loads it twice).
The reconciliation with the set-based routing model (on routes that repeat no arc,
its edge flow equals `edgeVolume`) lives in a separate bridge module in
`MathlibExt.GameTheory`, so this core module depends only on `ArcNetwork`.

Representation decision: the route representation of this module is the arc list with
`List.count` multiplicity. The vertex-pair path loads of
`MathlibExt.Probability.CanonicalPaths` are the analogous construction for canonical
paths between states; they are a different representation and are not reused here.

Link costs appear only as the fixed pairing of W3; no equilibria, capacities or algorithms are stated. The demand-side
consequences (OD balance and unreachability) live in
`MathlibExt.Combinatorics.Graph.ArcNetworkDemand`.
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

/-! ### Walk construction and decomposition

Building walks by prepending or appending arcs and lists, and reading a cons or append walk
back into its pieces. -/

/-- The empty arc list is a walk from an event to itself. -/
theorem walk_nil {V E : Type*} {tail head : E → V} {o : V} :
    IsArcWalk tail head o o [] := by
  refine ⟨fun _ => rfl, fun e he => by simp at he, List.isChain_nil, fun e he => by simp at he⟩

/-- A single arc from the origin to the destination is a walk between them. -/
theorem walk_singleton {V E : Type*} {tail head : E → V} {o d : V} {a : E}
    (ht : tail a = o) (hd : head a = d) : IsArcWalk tail head o d [a] := by
  refine ⟨fun h => by simp at h, fun e he => ?_, List.isChain_singleton a, fun e he => ?_⟩
  · simp at he
    subst he
    exact ht
  · simp at he
    subst he
    exact hd

/-- Prepending an arc leaving the origin to a walk out of its head gives a walk from the
origin, when the arc meets the first arc of the walk. -/
theorem walk_cons {V E : Type*} {tail head : E → V} {o d : V} {a : E} {l : List E}
    (ht : tail a = o) (htl : IsArcWalk tail head (head a) d l)
    (hchain : ∀ b ∈ l.head?, head a = tail b) : IsArcWalk tail head o d (a :: l) := by
  obtain ⟨hnil, -, hch, hlast⟩ := htl
  refine ⟨fun h => by simp at h, fun e he => ?_, List.isChain_cons.2 ⟨hchain, hch⟩,
    fun e he => ?_⟩
  · simp at he
    subst he
    exact ht
  · cases l with
    | nil =>
      simp at he
      subst he
      exact hnil rfl
    | cons b l' =>
      rw [List.getLast?_cons_cons] at he
      exact hlast e he

/-- Appending an arc entering the destination to a walk ending at its tail gives a walk
into the destination. -/
theorem walk_snoc {V E : Type*} {tail head : E → V} {o d : V} {l : List E} {a : E}
    (hp : IsArcWalk tail head o (tail a) l) (hd : head a = d) :
    IsArcWalk tail head o d (l ++ [a]) := by
  obtain ⟨hnil, hhead, hch, hlast⟩ := hp
  refine ⟨fun h => by simp at h, fun e he => ?_, ?_, fun e he => ?_⟩
  · cases l with
    | nil =>
      simp at he
      subst he
      exact (hnil rfl).symm
    | cons b l' =>
      simp at he
      subst he
      exact hhead b (by simp)
  · exact hch.append (List.isChain_singleton a) (fun x hx y hy => by
      simp at hy
      subst hy
      exact hlast x hx)
  · rw [List.getLast?_concat] at he
    simp at he
    subst he
    exact hd

/-- Dropping the first arc of a walk leaves a walk from that arc's head. -/
theorem walk_tail {V E : Type*} {tail head : E → V} {o d : V} {a : E} {l : List E}
    (h : IsArcWalk tail head o d (a :: l)) : IsArcWalk tail head (head a) d l := by
  obtain ⟨-, -, hch, hlast⟩ := h
  have hpair : ∀ b ∈ l.head?, head a = tail b := (List.isChain_cons.1 hch).1
  have hch' : l.IsChain (fun a b => head a = tail b) := (List.isChain_cons.1 hch).2
  refine ⟨?_, fun b hb => (hpair b hb).symm, hch', ?_⟩
  · intro hl
    subst hl
    exact hlast a (by simp)
  · cases l with
    | nil => intro e he; simp at he
    | cons b l' =>
      rw [List.getLast?_cons_cons] at hlast
      exact hlast

/-- A cons walk starts with an arc leaving the origin, and its tail is a walk from that
arc's head. -/
theorem walk_cons_pair {V E : Type*} {tail head : E → V} {o d : V} {a : E} {rest : List E}
    (hl : IsArcWalk tail head o d (a :: rest)) :
    tail a = o ∧ IsArcWalk tail head (head a) d rest := by
  obtain ⟨h1, h2, h3, h4⟩ := hl
  have htail : tail a = o := h2 a (by simp [List.head?_cons])
  refine ⟨htail, ?_, ?_, ?_, ?_⟩
  · intro hnil
    subst hnil
    exact h4 a (by simp [List.getLast?_singleton])
  · intro e he
    cases rest with
    | nil => simp at he
    | cons b rest' =>
        rw [List.head?_cons, Option.mem_some] at he
        cases he
        exact (List.isChain_cons_cons.mp h3).1.symm
  · cases rest with
    | nil => exact List.isChain_nil
    | cons b rest' => exact (List.isChain_cons_cons.mp h3).2
  · intro e he
    cases rest with
    | nil => simp at he
    | cons b rest' =>
        have hgl := List.getLast?_cons_of_ne_nil (x := a) (xs := b :: rest') (by simp)
        rw [hgl] at h4
        exact h4 e he

/-- Prepending an arc leaving the origin to a walk out of its head gives a walk from the origin. -/
theorem walk_cons_mk {V E : Type*} {tail head : E → V} {o m : V} {a : E}
    {rest : List E} (htail : tail a = o) (hr : IsArcWalk tail head (head a) m rest) :
    IsArcWalk tail head o m (a :: rest) := by
  obtain ⟨r1, r2, r3, r4⟩ := hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hnil
    cases hnil
  · intro e he
    rw [List.head?_cons, Option.mem_some] at he
    rw [← he]
    exact htail
  · cases rest with
    | nil => exact List.isChain_singleton a
    | cons b rest' =>
        have hb : tail b = head a := r2 b (by simp [List.head?_cons])
        have hr3 : (b :: rest').IsChain (fun x y => head x = tail y) := r3
        exact List.isChain_cons_cons.mpr ⟨hb.symm, hr3⟩
  · intro e he
    cases rest with
    | nil =>
        rw [List.getLast?_singleton, Option.mem_some] at he
        cases he
        exact r1 rfl
    | cons b rest' =>
        have hgl := List.getLast?_cons_of_ne_nil (x := a) (xs := b :: rest') (by simp)
        rw [hgl] at he
        exact r4 e he

/-- An append walk splits at some middle event into walks on the two parts. -/
theorem walk_append {V E : Type*} {tail head : E → V} {o d : V} {l1 l2 : List E}
    (hl : IsArcWalk tail head o d (l1 ++ l2)) :
    ∃ m, IsArcWalk tail head o m l1 ∧ IsArcWalk tail head m d l2 := by
  induction l1 generalizing o with
  | nil =>
      rw [List.nil_append] at hl
      refine ⟨o, ⟨?_, ?_, ?_, ?_⟩, hl⟩
      · intro _
        rfl
      · intro e he
        simp at he
      · exact List.isChain_nil
      · intro e he
        simp at he
  | cons a rest ih =>
      rw [List.cons_append] at hl
      obtain ⟨htail, hrest⟩ := walk_cons_pair hl
      obtain ⟨m, h1, h2⟩ := ih hrest
      exact ⟨m, walk_cons_mk htail h1, h2⟩

/-- Two walks meeting at a middle event concatenate to a walk on the appended list. -/
theorem walk_append_mk {V E : Type*} {tail head : E → V} {o m d : V} {l1 l2 : List E}
    (h1 : IsArcWalk tail head o m l1) (h2 : IsArcWalk tail head m d l2) :
    IsArcWalk tail head o d (l1 ++ l2) := by
  obtain ⟨h1e, h1h, h1c, h1t⟩ := h1
  obtain ⟨h2e, h2h, h2c, h2t⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hnil
    rw [List.append_eq_nil_iff] at hnil
    obtain ⟨rfl, rfl⟩ := hnil
    exact (h1e rfl).trans (h2e rfl)
  · intro e he
    cases l1 with
    | nil =>
        rw [List.nil_append] at he
        exact (h2h e he).trans (h1e rfl).symm
    | cons a rest =>
        rw [List.cons_append, List.head?_cons, Option.mem_some] at he
        rw [← he]
        exact h1h a (by simp [List.head?_cons])
  · exact List.IsChain.append h1c h2c (fun x hx y hy => (h1t x hx).trans (h2h y hy).symm)
  · intro e he
    cases l2 with
    | nil =>
        rw [List.append_nil] at he
        exact (h1t e he).trans (h2e rfl)
    | cons b rest' =>
        rw [List.getLast?_append] at he
        cases hX : (b :: rest').getLast? with
        | none =>
            rw [List.getLast?_eq_none_iff] at hX
            cases hX
        | some x =>
            rw [hX] at he
            have he' : e ∈ (b :: rest').getLast? := by rw [hX]; exact he
            exact h2t e he'

/-- Total travel time on supplied routes, path side equals edge side: with link travel times
`t` fixed at the induced volumes `x = edgeVolume edges f`, the flow-weighted sum of route
travel times `∑ p, f p * ((edges p).map fun e => t e (x e)).sum` equals `∑ e, x e * t e (x e)`.
A route that traverses an arc twice pays its cost twice and loads it twice. Units:
vehicle-flow times time on both sides. With constant `t e _ = c e` this is the identity for
any fixed edge costs `c`. -/
theorem sum_mul_sum_map_eq_sum_edgeVolume_mul {P E : Type*} [Fintype P] [Fintype E]
    [DecidableEq E] (edges : P → List E) (f : P → ℝ) (t : E → ℝ → ℝ) :
    ∑ p, f p * ((edges p).map fun e => t e (edgeVolume edges f e)).sum =
      ∑ e, edgeVolume edges f e * t e (edgeVolume edges f e) := by
  have h1 : ∀ p : P, f p * ((edges p).map fun e => t e (edgeVolume edges f e)).sum
      = ∑ e, f p * ((((edges p).count e : ℕ) : ℝ) * t e (edgeVolume edges f e)) := by
    intro p
    have hext : (∑ e ∈ (edges p).toFinset,
          f p * ((((edges p).count e : ℕ) : ℝ) * t e (edgeVolume edges f e)))
        = ∑ e, f p * ((((edges p).count e : ℕ) : ℝ) * t e (edgeVolume edges f e)) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e _ he
      rw [List.mem_toFinset] at he
      rw [List.count_eq_zero_of_not_mem he]
      simp
    rw [← hext, Finset.sum_list_map_count, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [nsmul_eq_mul]
  have hLHS : (∑ p, f p * ((edges p).map fun e => t e (edgeVolume edges f e)).sum)
      = ∑ p, ∑ e, f p * ((((edges p).count e : ℕ) : ℝ) * t e (edgeVolume edges f e)) :=
    Finset.sum_congr rfl (fun p _ => h1 p)
  rw [hLHS, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [edgeVolume]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  exact (mul_assoc _ _ _).symm

end MathlibExt.Combinatorics.Graph.ArcNetwork
