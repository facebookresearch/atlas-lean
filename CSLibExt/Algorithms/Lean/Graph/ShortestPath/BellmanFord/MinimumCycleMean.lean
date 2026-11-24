/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic
public import Mathlib.Data.Rat.Defs
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Linarith

/-!
# Karp's characterization of the minimum cycle mean

This module proves Karp's minimum cycle mean formula for integer-weighted directed graphs.

Karp, *A characterization of the minimum cycle mean in a digraph*, Discrete Mathematics 23 (1978)
309–311, Theorem 1. Let `G` be a strongly connected digraph with `n` vertices and edge weights,
let `λ*` be the minimum, over the directed cycles `C` of `G`, of the mean weight `w(C) / |C|`,
fix a vertex `s`, and let `F_k(v)` be the minimum weight of an edge progression (a walk) with `k`
edges from `s` to `v`, or `∞` when there is none. Then
`λ* = min_v max_{0 ≤ k ≤ n - 1} (F_n(v) - F_k(v)) / (n - k)`.

The statement uses the weighted edge lists of `CSLibExt.Algorithms.Lean.Graph.ShortestPath.
BellmanFord.Basic`: edge occurrences with integer weights (Karp allows real weights), walks as
lists of edge occurrences (`IsWeightedPath`) and their weights (`pathWeight`). The value
`F_k(v)` is described by the predicate `IsMinWalkWeight` (it holds of `x` exactly when
`F_k(v) = x` is finite), and the formula is split into the two inequalities that make the
`min max` equal to `λ*`, with Karp's conventions for infinite values: a vertex with
`F_n(v) = ∞` contributes `+∞` to the outer minimum, and an index with `F_k(v) = ∞` contributes
`-∞` to the inner maximum. The algorithm computing `F_k` by the Bellman–Ford recurrence in
`O(n |E|)` steps (same paper, p. 310) is not stated.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFord

@[expose] public section

/-- **Directed cycle in a weighted edge list.** A nonempty walk from `v` back to `v` whose vertices,
the starting vertex counted once, are pairwise distinct (Karp, Discrete Math. 23 (1978),
p. 309: the directed cycles over which the minimum cycle mean is taken). -/
def IsDirectedCycle {n : ℕ} (edges : List (Edge n)) (v : Fin n) (cycle : List (Edge n)) :
    Prop :=
  IsWeightedPath edges v v cycle ∧ cycle ≠ [] ∧ (pathVertices v cycle).tail.Nodup

/-- **Minimum cycle mean.** `λ` is the minimum of `w(C) / |C|` over the directed cycles `C`: it is
attained by a cycle, and no cycle has a smaller mean weight (Karp, Discrete Math. 23 (1978),
p. 309). -/
def IsMinCycleMean {n : ℕ} (edges : List (Edge n)) (lam : ℚ) : Prop :=
  (∃ v cycle, IsDirectedCycle edges v cycle ∧ (pathWeight cycle : ℚ) / cycle.length = lam) ∧
    ∀ v cycle, IsDirectedCycle edges v cycle → lam ≤ (pathWeight cycle : ℚ) / cycle.length

/-- **Minimum weight of a walk with `k` edges.** `x` is the minimum weight of an edge progression
with exactly `k` edges from `s` to `v`: some such walk has weight `x` and none has a smaller
weight. This is Karp's `F_k(v) = x`; when no such walk exists, `F_k(v) = ∞` and the predicate
holds of no `x` (Karp, Discrete Math. 23 (1978), p. 309). -/
def IsMinWalkWeight {n : ℕ} (edges : List (Edge n)) (s v : Fin n) (k : ℕ) (x : ℤ) : Prop :=
  (∃ walk, IsWeightedPath edges s v walk ∧ walk.length = k ∧ pathWeight walk = x) ∧
    ∀ walk, IsWeightedPath edges s v walk → walk.length = k → x ≤ pathWeight walk

end

namespace karp_minCycleMean

variable {n : ℕ} {edges : List (Edge n)} {s v u : Fin n}

private lemma path_append_iff {left right : List (Edge n)} :
    IsWeightedPath edges s v (left ++ right) ↔
      ∃ u, IsWeightedPath edges s u left ∧ IsWeightedPath edges u v right := by
  induction left generalizing s with
  | nil =>
    simp [IsWeightedPath, List.nil_append]
  | cons e left ih =>
    constructor
    · intro hp
      obtain ⟨u, hl, hr⟩ := ih.mp (isWeightedPath_tail hp)
      exact ⟨u, Internal.isWeightedPath_cons (hp.1 e (by simp)) hp.2.2.1 hl, hr⟩
    · rintro ⟨u, hl, hr⟩
      exact Internal.isWeightedPath_cons (hl.1 e (by simp)) hl.2.2.1
        (ih.mpr ⟨u, isWeightedPath_tail hl, hr⟩)

private lemma path_append {left right : List (Edge n)}
    (hl : IsWeightedPath edges s u left) (hr : IsWeightedPath edges u v right) :
    IsWeightedPath edges s v (left ++ right) :=
  path_append_iff.mpr ⟨u, hl, hr⟩

-- Inspect the first repeated vertex encountered when reading the walk backwards.
private lemma erase_cycle {p : List (Edge n)} (hp : IsWeightedPath edges s v p)
    (hd : ¬ (pathVertices s p).Nodup) :
    ∃ u c q, IsDirectedCycle edges u c ∧ IsWeightedPath edges s v q ∧
      q.length + c.length = p.length ∧ pathWeight q + pathWeight c = pathWeight p := by
  induction p generalizing s with
  | nil => simp [pathVertices] at hd
  | cons e rest ih =>
    have he := hp.1 e (by simp)
    have hs := hp.2.2.1
    have hr := isWeightedPath_tail hp
    by_cases hd' : (pathVertices e.target rest).Nodup
    · have hmem : s ∈ (e :: rest).map Edge.target := by
        by_contra hn
        exact hd (List.nodup_cons.mpr ⟨hn, hd'⟩)
      obtain ⟨f, hf, htarget⟩ := List.mem_map.mp hmem
      obtain ⟨a, b, hab⟩ := List.append_of_mem hf
      have hp' : IsWeightedPath edges s v ((a ++ [f]) ++ b) := by
        simpa [List.append_assoc] using hab ▸ hp
      obtain ⟨middle, ha, hb⟩ := path_append_iff.mp hp'
      have hmiddle : middle = s := by
        have hlast := (Internal.isWeightedPath_append_edge_iff.mp ha).2.2
        exact hlast.symm.trans htarget
      subst middle
      have hcycle : IsDirectedCycle edges s (a ++ [f]) := by
        refine ⟨ha, by simp, ?_⟩
        change ((a ++ [f]).map Edge.target).Nodup
        have htargets : ((e :: rest).map Edge.target).Nodup := hd'
        rw [hab, show a ++ f :: b = (a ++ [f]) ++ b by simp, List.map_append] at htargets
        exact htargets.sublist (List.sublist_append_left _ _)
      exact ⟨s, a ++ [f], b, hcycle, hb, by simp [hab]; omega,
        by simp [hab, pathWeight]; omega⟩
    · obtain ⟨u, c, q, hc, hq, hlen, hw⟩ := ih hr hd'
      exact ⟨u, c, e :: q, hc, Internal.isWeightedPath_cons he hs hq,
        by simp; omega, by simp [pathWeight] at *; omega⟩

private def shiftedWeight (lam : ℚ) (p : List (Edge n)) : ℚ :=
  (pathWeight p : ℚ) - lam * p.length

private lemma shiftedWeight_append (lam : ℚ) (a b : List (Edge n)) :
    shiftedWeight lam (a ++ b) = shiftedWeight lam a + shiftedWeight lam b := by
  simp [shiftedWeight, pathWeight, mul_add]
  linarith

-- Erase cycles until the walk visits at most n distinct vertices.
private lemma exists_short_walk {lam : ℚ} (hlam : IsMinCycleMean edges lam)
    {p : List (Edge n)} (hp : IsWeightedPath edges s v p) :
    ∃ q, IsWeightedPath edges s v q ∧ q.length < n ∧
      shiftedWeight lam q ≤ shiftedWeight lam p := by
  by_cases hsimple : (pathVertices s p).Nodup
  · have hcard := hsimple.length_le_card
    simp [pathVertices] at hcard
    exact ⟨p, hp, by omega, le_rfl⟩
  · obtain ⟨u, c, q, hc, hq, hlen, hw⟩ := erase_cycle hp hsimple
    have hcpos : 0 < c.length := List.length_pos_iff.mpr hc.2.1
    have hnonneg : 0 ≤ shiftedWeight lam c := by
      have h := (le_div_iff₀ (by exact_mod_cast hcpos)).mp (hlam.2 u c hc)
      exact sub_nonneg.mpr h
    have hsplit : shiftedWeight lam q + shiftedWeight lam c = shiftedWeight lam p := by
      unfold shiftedWeight
      rw [← hlen, ← hw, Nat.cast_add, Int.cast_add, mul_add]
      linarith
    obtain ⟨r, hr, hlt, hweight⟩ := exists_short_walk hlam hq
    exact ⟨r, hr, hlt, by linarith⟩
termination_by p.length
decreasing_by omega

private lemma finite_walks (k : ℕ) :
    {p : List (Edge n) | IsWeightedPath edges s v p ∧ p.length ≤ k}.Finite := by
  let EdgeIn := {e : Edge n // e ∈ edges}
  let : Fintype EdgeIn :=
    Fintype.ofFinset (p := {e | e ∈ edges}) edges.toFinset (by simp)
  refine ((List.finite_length_le EdgeIn k).image (List.map Subtype.val)).subset ?_
  rintro p ⟨hp, hlen⟩
  refine ⟨p.pmap (fun e he ↦ (⟨e, he⟩ : EdgeIn)) hp.1, ?_, ?_⟩
  · change (List.pmap _ p hp.1).length ≤ k
    rwa [List.length_pmap]
  · rw [List.map_pmap]
    exact List.pmap_eq_self.mpr fun _ _ ↦ rfl

private lemma exists_min_walk_weight {p : List (Edge n)} (hp : IsWeightedPath edges s v p) :
    ∃ x, IsMinWalkWeight edges s v p.length x := by
  let walks := {q : List (Edge n) | IsWeightedPath edges s v q ∧ q.length = p.length}
  have hfinite : walks.Finite :=
    (finite_walks p.length).subset fun _ h ↦ ⟨h.1, h.2.le⟩
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image walks pathWeight hfinite ⟨p, hp, rfl⟩
  exact ⟨pathWeight q, ⟨q, hq.1, hq.2, rfl⟩, fun r hr hlen ↦ hmin r ⟨hr, hlen⟩⟩

private lemma exists_min_shifted_weight {lam : ℚ} (hlam : IsMinCycleMean edges lam)
    (hreach : (toDirectedAdjacency edges).Reachable s v) :
    ∃ p, IsWeightedPath edges s v p ∧
      ∀ q, IsWeightedPath edges s v q → shiftedWeight lam p ≤ shiftedWeight lam q := by
  obtain ⟨walk, hwalk⟩ := reachable_iff_exists_isWeightedPath.mp hreach
  obtain ⟨short, hshort, hlen, _⟩ := exists_short_walk hlam hwalk
  let walks := {q : List (Edge n) | IsWeightedPath edges s v q ∧ q.length ≤ n}
  obtain ⟨p, hp, hmin⟩ :=
    Set.exists_min_image walks (shiftedWeight lam) (finite_walks n) ⟨short, hshort, hlen.le⟩
  refine ⟨p, hp.1, fun q hq ↦ ?_⟩
  obtain ⟨r, hr, hrl, hrw⟩ := exists_short_walk hlam hq
  exact (hmin r ⟨hr, hrl.le⟩).trans hrw

private lemma repeat_zero_cycle {lam : ℚ} {c : List (Edge n)}
    (hc : IsDirectedCycle edges v c) (hw : shiftedWeight lam c = 0) (k : ℕ) :
    ∃ q, IsWeightedPath edges v v q ∧ k ≤ q.length ∧ shiftedWeight lam q = 0 := by
  induction k with
  | zero =>
    exact ⟨[], by simp [IsWeightedPath], Nat.zero_le _, by simp [shiftedWeight, pathWeight]⟩
  | succ k ih =>
    obtain ⟨q, hq, hlen, hqweight⟩ := ih
    have hcpos : 0 < c.length := List.length_pos_iff.mpr hc.2.1
    exact ⟨q ++ c, path_append hq hc.1, by simp; omega,
      by rw [shiftedWeight_append, hw, hqweight, add_zero]⟩

-- Extending a shortest walk by copies of a zero-weight cycle preserves minimality.
-- Every prefix is then shortest to its own endpoint because a cheaper prefix
-- could be followed by the same suffix.
private lemma exists_min_shifted_weight_of_length {lam : ℚ} (hlam : IsMinCycleMean edges lam)
    (strong : ∀ u v, (toDirectedAdjacency edges).Reachable u v) (k : ℕ) :
    ∃ v p, IsWeightedPath edges s v p ∧ p.length = k ∧
      ∀ q, IsWeightedPath edges s v q → shiftedWeight lam p ≤ shiftedWeight lam q := by
  obtain ⟨base, c, hc, hmean⟩ := hlam.1
  have hcpos : 0 < c.length := List.length_pos_iff.mpr hc.2.1
  have hzero : shiftedWeight lam c = 0 := by
    have h := (div_eq_iff (by exact_mod_cast hcpos.ne')).mp hmean
    exact sub_eq_zero.mpr h
  obtain ⟨short, hshort, hmin⟩ := exists_min_shifted_weight hlam (strong s base)
  obtain ⟨rounds, hrounds, hlen, hw⟩ := repeat_zero_cycle hc hzero k
  let walk := short ++ rounds
  have hwalk : IsWeightedPath edges s base walk := path_append hshort hrounds
  have hwalklen : k ≤ walk.length := by simp [walk]; omega
  have hwalkweight : shiftedWeight lam walk = shiftedWeight lam short := by
    rw [show walk = short ++ rounds from rfl, shiftedWeight_append, hw, add_zero]
  have hsplit : IsWeightedPath edges s base (walk.take k ++ walk.drop k) := by
    simpa only [List.take_append_drop] using hwalk
  obtain ⟨v, hp, hsuffix⟩ := path_append_iff.mp hsplit
  refine ⟨v, walk.take k, hp, by simp [List.length_take, min_eq_left hwalklen], ?_⟩
  intro q hq
  have hlo := hmin (q ++ walk.drop k) (path_append hq hsuffix)
  rw [shiftedWeight_append, ← hwalkweight] at hlo
  have hparts : shiftedWeight lam (walk.take k) + shiftedWeight lam (walk.drop k) =
      shiftedWeight lam walk := by
    rw [← shiftedWeight_append, List.take_append_drop]
  rw [← hparts] at hlo
  exact le_of_add_le_add_right hlo

end karp_minCycleMean

@[expose] public section

/-- **Karp's minimum cycle mean theorem.** Let the digraph of `edges`, on `n` vertices, be strongly
connected, let `λ` be its minimum cycle mean, and let `s` be a vertex. Then
`λ = min_v max_{0 ≤ k ≤ n - 1} (F_n(v) - F_k(v)) / (n - k)`, in the following form: every vertex
`v` with `F_n(v)` finite has an index `k < n` with `F_k(v)` finite and
`(F_n(v) - F_k(v)) / (n - k) ≥ λ`; and some vertex `v` with `F_n(v)` finite has
`(F_n(v) - F_k(v)) / (n - k) ≤ λ` for every `k < n` with `F_k(v)` finite (Karp, Discrete
Mathematics 23 (1978), Theorem 1, for integer weights). -/
theorem karp_minCycleMean {n : ℕ} (edges : List (Edge n))
    (strong : ∀ u v, (toDirectedAdjacency edges).Reachable u v) (s : Fin n) (lam : ℚ)
    (hlam : IsMinCycleMean edges lam) :
    (∀ v x, IsMinWalkWeight edges s v n x →
      ∃ k < n, ∃ y, IsMinWalkWeight edges s v k y ∧
        lam ≤ ((x - y : ℤ) : ℚ) / ((n - k : ℕ) : ℚ)) ∧
    ∃ v x, IsMinWalkWeight edges s v n x ∧
      ∀ k < n, ∀ y, IsMinWalkWeight edges s v k y →
        ((x - y : ℤ) : ℚ) / ((n - k : ℕ) : ℚ) ≤ lam := by
  constructor
  · intro v x hx
    obtain ⟨p, hp, hplen, hpweight⟩ := hx.1
    obtain ⟨q, hq, hqlen, hle⟩ := karp_minCycleMean.exists_short_walk hlam hp
    obtain ⟨y, hy⟩ := karp_minCycleMean.exists_min_walk_weight hq
    refine ⟨q.length, hqlen, y, hy, ?_⟩
    have hden : (0 : ℚ) < ((n - q.length : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_pos_of_lt hqlen
    have hyq : (y : ℚ) ≤ (pathWeight q : ℚ) := by exact_mod_cast hy.2 q hq rfl
    rw [le_div_iff₀ hden, Int.cast_sub, Nat.cast_sub hqlen.le]
    simp only [karp_minCycleMean.shiftedWeight, hplen, hpweight] at hle
    linarith
  · obtain ⟨v, p, hp, hplen, hmin⟩ :=
      karp_minCycleMean.exists_min_shifted_weight_of_length (s := s) hlam strong n
    refine ⟨v, pathWeight p, ⟨⟨p, hp, hplen, rfl⟩, ?_⟩, ?_⟩
    · intro q hq hqlen
      have hle := hmin q hq
      simp only [karp_minCycleMean.shiftedWeight, hplen, hqlen] at hle
      exact_mod_cast ((sub_le_sub_iff_right _).mp hle)
    · intro k hk y hy
      obtain ⟨q, hq, hqlen, hqweight⟩ := hy.1
      have hle := hmin q hq
      have hden : (0 : ℚ) < ((n - k : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hk
      rw [div_le_iff₀ hden, Int.cast_sub, Nat.cast_sub hk.le]
      simp only [karp_minCycleMean.shiftedWeight, hplen, hqlen, hqweight] at hle
      linarith

end

end Cslib.Algorithms.Lean.BellmanFord
