/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Nat.Find

/-!
# Longest cycles in simple graphs

This file provides the predicate that a closed walk is a cycle of maximum
length among all cycles in the same graph, a vertex-count bound on cycle
length, and the existence of a longest cycle from any seed cycle.
-/

@[expose] public section

namespace SimpleGraph.Walk

/-- A cycle is globally longest if no cycle in the graph has more edges. -/
public def IsLongestCycle {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) : Prop :=
  p.IsCycle ∧ ∀ (w : V) (q : G.Walk w w), q.IsCycle → q.length ≤ p.length

/-- A cycle has length at most the number of vertices. -/
public theorem IsCycle.length_le_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  have hnodup := hc.isPath_tail.support_nodup
  have hcard := hnodup.length_le_card
  have hlen : c.tail.support.length = c.length := by
    rw [c.support_tail_of_not_nil hc.not_nil, List.length_tail, Walk.length_support]
    omega
  omega

/-- If a graph has a cycle, it has a longest cycle. -/
public theorem exists_isLongestCycle {V : Type*} [Finite V] {G : SimpleGraph V}
    {x : V} (c₀ : G.Walk x x) (hc₀ : c₀.IsCycle) :
    ∃ (w : V) (c : G.Walk w w), c.IsLongestCycle := by
  classical
  have := Fintype.ofFinite V
  have hP0 : ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ 0 ≤ c.length :=
    ⟨x, c₀, hc₀, Nat.zero_le _⟩
  set m := Nat.findGreatest
    (fun k => ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ k ≤ c.length)
    (Fintype.card V) with hm
  have hPm : ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ m ≤ c.length :=
    Nat.findGreatest_spec
      (P := fun k => ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ k ≤ c.length)
      (Nat.zero_le _) hP0
  obtain ⟨w, c, hc, hmc⟩ := hPm
  refine ⟨w, c, hc, fun w' q hq => ?_⟩
  have hle : q.length ≤ Fintype.card V := hq.length_le_card
  have hqm : q.length ≤ m :=
    Nat.le_findGreatest (P := fun k => ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ k ≤ c.length)
      hle ⟨w', q, hq, le_refl _⟩
  omega

end SimpleGraph.Walk
