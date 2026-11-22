/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.RandomCurrent
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Backbones of random currents

Parity of vertex degrees along paths, properties of backbone paths, and removal of a backbone from a
current.

## i. Overview

Along a path from `a` to `b`, a vertex has odd degree iff it is an endpoint and `a ≠ b`. A backbone
path uses only edges with odd (hence positive) current, so its endpoints are connected in the
current. Removing the backbone from a current with sources `{a, b}` leaves a sourceless current.

## ii. Key results

- `walkDeg` : degree of a vertex along a walk
- `walkDeg_odd_iff` : parity of degrees along a path
- `isBackbonePath_edge_odd` : backbone edges carry odd current
- `removeWalk` : removal of a walk from a current
- `sources_removeWalk_eq_empty` : removing the backbone leaves no sources

## iii. Table of contents

- A. Degrees along walks
- B. Backbone paths
- C. Removing a backbone

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48

-/

@[expose] public section

open SimpleGraph Finset


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {H : SimpleGraph V}

/-! ## A. Degrees along walks -/

/-- The number of edges of the walk `p` incident to `x`. -/
def walkDeg {a b : V} (p : H.Walk a b) (x : V) : ℕ :=
  (p.edges.filter (fun e => x ∈ e)).length

omit [Fintype V] in
@[simp]
lemma walkDeg_nil {a : V} (x : V) : walkDeg (Walk.nil : H.Walk a a) x = 0 := by
  simp [walkDeg]

omit [Fintype V] in
lemma walkDeg_cons {u v w : V} (h : H.Adj u v) (p : H.Walk v w) (x : V) :
    walkDeg (Walk.cons h p) x
      = (if x ∈ (s(u, v) : Sym2 V) then 1 else 0) + walkDeg p x := by
  unfold walkDeg
  rw [Walk.edges_cons, List.filter_cons]
  by_cases hx : x ∈ (s(u, v) : Sym2 V) <;> simp [hx, add_comm]

omit [Fintype V] in
lemma walkDeg_eq_zero_of_not_support {a b : V} (p : H.Walk a b) (x : V)
    (hx : x ∉ p.support) : walkDeg p x = 0 := by
  unfold walkDeg
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he
  simp only [decide_eq_true_eq]
  intro hxe
  exact hx (Walk.mem_support_of_mem_edges he hxe)

omit [Fintype V] in
lemma walkDeg_odd_iff {a b : V} (p : H.Walk a b) (hp : p.IsPath) (x : V) :
    Odd (walkDeg p x) ↔ (x = a ∨ x = b) ∧ a ≠ b := by
  induction p with
  | nil =>
    simp only [walkDeg_nil]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨_, hne⟩; exact absurd rfl hne
  | @cons a v b h p ih =>
    have hpp : p.IsPath := hp.of_cons
    have hav : a ≠ v := h.ne
    have ha_not : a ∉ p.support := by
      have := hp.support_nodup
      rw [Walk.support_cons, List.nodup_cons] at this
      exact this.1
    have hb_supp : b ∈ p.support := Walk.end_mem_support p
    have hab : a ≠ b := fun heq => ha_not (heq ▸ hb_supp)
    have iff_p := ih hpp
    rw [walkDeg_cons]
    by_cases hc : x ∈ (s(a, v) : Sym2 V)
    · rw [ite_eq_left hc]
      rw [Sym2.mem_iff] at hc
      rcases hc with rfl | rfl
      · rw [walkDeg_eq_zero_of_not_support p x ha_not]
        constructor
        · intro _; exact ⟨Or.inl rfl, hab⟩
        · intro _; exact ⟨0, rfl⟩
      · rw [add_comm, Nat.odd_add_one, iff_p]
        constructor
        · intro h1
          have hxb : x = b := not_not.mp fun hne => h1 ⟨Or.inl rfl, hne⟩
          exact ⟨Or.inr hxb, hab⟩
        · rintro ⟨hor, _⟩
          rcases hor with h1 | h1
          · exact absurd h1.symm hav
          · intro ⟨_, hne⟩; exact hne h1
    · rw [ite_eq_right hc, zero_add]
      rw [Sym2.mem_iff] at hc
      obtain ⟨hxa, hxv⟩ := not_or.mp hc
      rw [iff_p]
      constructor
      · rintro ⟨hor, _⟩
        rcases hor with h1 | h1
        · exact absurd h1 hxv
        · exact ⟨Or.inr h1, hab⟩
      · rintro ⟨hor, _⟩
        rcases hor with h1 | h1
        · exact absurd h1 hxa
        · exact ⟨Or.inr h1, fun hvb => hxv (h1.trans hvb.symm)⟩

lemma sum_count_eq_walkDeg {a b : V} (p : H.Walk a b) (x : V)
    (hsub : ∀ e ∈ p.edges, e ∈ G.edgeFinset) :
    ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e), (p.edges).count e = walkDeg p x := by
  classical
  simp only [← Multiset.coe_count]
  have step1 : ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e),
        Multiset.count e (p.edges : Multiset (Sym2 V))
      = ∑ e ∈ G.edgeFinset,
        Multiset.count e (Multiset.filter (fun e => x ∈ e) (p.edges : Multiset (Sym2 V))) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun e _ => by rw [Multiset.count_filter])
  rw [step1, Multiset.sum_count_eq_card]
  · unfold walkDeg
    rw [Multiset.filter_coe]
    rfl
  · intro e he
    rw [Multiset.mem_filter] at he
    exact hsub e he.1

/-! ## B. Backbone paths -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma isBackbonePath_edge_odd {n : Current V} {a b : V}
    (p : IsBackbonePath G n a b) {e : Sym2 V} (he : e ∈ p.1.edges) : Odd (n e) := by
  have h1 : e ∈ (oddSubgraph G n).edgeSet := p.1.edges_subset_edgeSet he
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at h1
    exact h1.2

omit [DecidableEq V] in
lemma isBackbonePath_edge_mem {n : Current V} {a b : V}
    (p : IsBackbonePath G n a b) {e : Sym2 V} (he : e ∈ p.1.edges) :
    e ∈ G.edgeFinset := by
  have h1 : e ∈ (oddSubgraph G n).edgeSet := p.1.edges_subset_edgeSet he
  rw [mem_edgeFinset]
  exact SimpleGraph.edgeSet_mono (oddSubgraph_le G n) h1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma isBackbonePath_edge_pos {n : Current V} {a b : V}
    (p : IsBackbonePath G n a b) {e : Sym2 V} (he : e ∈ p.1.edges) : 1 ≤ n e :=
  (isBackbonePath_edge_odd G p he).pos

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma isBackbonePath_currentConnected {n : Current V} {a b : V}
    (p : IsBackbonePath G n a b) : CurrentConnected G n a b :=
  IsBackbonePath.currentConnected G p

lemma backbone_currentConnected (n : Current V) (a b : V)
    [LinearOrder (IsBackbonePath G n a b)]
    (h : Nonempty (IsBackbonePath G n a b)) :
    CurrentConnected G n a b :=
  isBackbonePath_currentConnected G (backbone G n a b h)

lemma backbone_edge_odd (n : Current V) (a b : V)
    [LinearOrder (IsBackbonePath G n a b)]
    (h : Nonempty (IsBackbonePath G n a b)) {e : Sym2 V}
    (he : e ∈ (backbone G n a b h).1.edges) : Odd (n e) :=
  isBackbonePath_edge_odd G (backbone G n a b h) he

/-! ## C. Removing a backbone -/

/-- The current `n` with one unit removed from each traversal of an edge of `p`. -/
def removeWalk {a b : V} (n : Current V) (p : H.Walk a b) : Current V :=
  fun e => n e - p.edges.count e

omit [Fintype V] in
@[simp]
lemma removeWalk_apply {a b : V} (n : Current V) (p : H.Walk a b) (e : Sym2 V) :
    removeWalk n p e = n e - p.edges.count e := rfl

lemma incidentFlux_removeWalk {a b : V} (n : Current V) (p : H.Walk a b)
    (hsub : ∀ e ∈ p.edges, e ∈ G.edgeFinset)
    (hle : ∀ e ∈ G.edgeFinset, p.edges.count e ≤ n e) (x : V) :
    incidentFlux G (removeWalk n p) x = incidentFlux G n x - walkDeg p x := by
  unfold incidentFlux
  simp only [removeWalk_apply]
  rw [Finset.sum_tsub_distrib]
  · rw [sum_count_eq_walkDeg G p x hsub]
  · intro e he
    rw [Finset.mem_filter] at he
    exact hle e he.1

lemma sources_removeWalk_eq_empty {n : Current V} {a b : V}
    (p : IsBackbonePath G n a b) (hab : a ≠ b)
    (hsrc : sources G n = {a, b}) :
    sources G (removeWalk n p.1) = ∅ := by
  classical
  have hsub : ∀ e ∈ p.1.edges, e ∈ G.edgeFinset :=
    fun e he => isBackbonePath_edge_mem G p he
  have htrail : p.1.IsTrail := p.2.isTrail
  have hle : ∀ e ∈ G.edgeFinset, p.1.edges.count e ≤ n e := by
    intro e _
    by_cases hmem : e ∈ p.1.edges
    · calc p.1.edges.count e ≤ 1 := htrail.count_edges_le_one e
        _ ≤ n e := isBackbonePath_edge_pos G p hmem
    · rw [List.count_eq_zero_of_not_mem hmem]; exact Nat.zero_le _
  have hsrc_iff : ∀ x : V, Odd (incidentFlux G n x) ↔ (x = a ∨ x = b) := by
    intro x
    have : x ∈ sources G n ↔ x ∈ ({a, b} : Finset V) := by rw [hsrc]
    rw [mem_sources, Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_sources] at hx
  rw [incidentFlux_removeWalk G n p.1 hsub hle x] at hx
  have hwalk : Odd (walkDeg p.1 x) ↔ (x = a ∨ x = b) := by
    rw [walkDeg_odd_iff p.1 p.2 x]
    exact ⟨fun h => h.1, fun h => ⟨h, hab⟩⟩
  have hsame : Odd (incidentFlux G n x) ↔ Odd (walkDeg p.1 x) := by
    rw [hsrc_iff x, hwalk]
  have hge : walkDeg p.1 x ≤ incidentFlux G n x := by
    rw [← sum_count_eq_walkDeg G p.1 x hsub]
    unfold incidentFlux
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mem_filter] at he
    exact hle e he.1
  have heven : Even (incidentFlux G n x - walkDeg p.1 x) := by
    rw [Nat.even_sub hge, ← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, hsame]
  exact (Nat.not_odd_iff_even.mpr heven) hx

end Sharpness

end StatMech
