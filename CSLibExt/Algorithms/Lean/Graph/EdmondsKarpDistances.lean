/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.EdmondsKarp

/-!
# Residual distances never decrease under shortest-path augmentation

Edmonds and Karp, *Theoretical improvements in algorithmic efficiency for network flow
problems*, J. ACM 19(2) (1972) 248–264, §1.2. Let `f^{k+1}` be obtained from `f^k` by
augmenting along a shortest directed path `P^k` from `s` to `t` in the residual network
`N^k`, and let `δ^k(u, v)` be the distance from `u` to `v` in `N^k`.

* Proposition 2: every arc of `N^{k+1}` is an arc of `N^k` or the reverse of an arc of `P^k`.
  Here: `residualGraph_edge_augment`, for the skew-flow representation of
  `CSLibExt.Algorithms.Lean.Graph.EdmondsKarp` and any nonnegative augmentation amount.
* Proposition 3: `δ^k(s, u) ≤ δ^{k+1}(s, u)` and `δ^k(u, t) ≤ δ^{k+1}(u, t)` for every node `u`.
  The combinatorial core holds for any two relations `r`, `r'` such that every `r'`-step is an
  `r`-step or reverses a step of a shortest `r`-chain from `s` to `t`
  (`relatesWithinSteps_source_of_shortest`, `relatesWithinSteps_sink_of_shortest`); it is then
  applied to one step of the repository's algorithm (`walk_step_source`, `walk_step_sink`) and
  restated with its breadth-first-search distances (`bfs_distance_source_le_step`,
  `bfs_distance_sink_le_step`).

Distances are expressed through CSLib's exact-length walks `Relation.RelatesInSteps` and
bounded-length walks `Relation.RelatesWithinSteps`: "`δ^k(s, u) ≤ h` whenever `δ^{k+1}(s, u) = h`"
becomes "every walk of length `h` in `N^{k+1}` can be replaced by a walk of length at most `h`
in `N^k`", which also covers unreachable nodes (distance `∞`).

The paper's Theorem 1, the bound of `(n³ - n) / 4` augmentations, uses Proposition 3 through its
Lemmas 1 and 2; it is proved in `CSLibExt.Algorithms.Lean.Graph.EdmondsKarpAugmentationBound`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EdmondsKarp

open DirectedAdjacency BreadthFirstSearch Relation

section Chains

variable {α : Type*} {r r' : α → α → Prop}

/-- **A step of a chain splits it into two walks.** If `(a, b)` is a pair of consecutive entries
of an `r`-chain `p` from `s` to `t`, then there are walks from `s` to `a` and from `b` to `t`
whose lengths `i` and `j` satisfy `|p| = i + j + 2`, and `r a b` holds. -/
theorem exists_split_of_mem_pathEdges : ∀ {p : List α} {s t a b : α},
    p.IsChainFromTo r s t → (a, b) ∈ pathEdges p →
    ∃ i j, RelatesInSteps r s a i ∧ r a b ∧ RelatesInSteps r b t j ∧ p.length = i + j + 2
  | [], _, _, _, _, _, h => by simp [pathEdges] at h
  | [_], _, _, _, _, _, h => by simp [pathEdges] at h
  | x :: y :: rest, s, t, a, b, hp, h => by
    have hxs : x = s := hp.head_eq
    have hxy : r x y := (List.isChain_cons_cons.mp hp.isChain).1
    have htail := hp.of_cons_cons
    simp only [pathEdges, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · subst hxs
      exact ⟨0, rest.length, .refl _, hxy, htail.relatesInSteps (by simp), by simp⟩
    · obtain ⟨i, j, hi, hab, hj, hlen⟩ := exists_split_of_mem_pathEdges htail h
      subst hxs
      exact ⟨i + 1, j, RelatesInSteps.head _ _ _ _ hxy hi, hab, hj, by simp at hlen ⊢; omega⟩

/-- **Distances from the source do not decrease (abstract form of Edmonds–Karp,
Proposition 3 (1)).** Let `p` be a shortest `r`-chain from `s` to `t`, with `L + 1` entries, and
suppose every `r'`-step is an `r`-step or the reverse of a step of `p`. Then every `r'`-walk of
length `k` from `s` to `u` can be replaced by an `r`-walk of length at most `k` from `s` to `u`;
that is, the `r`-distance from `s` to `u` is at most the `r'`-distance (Edmonds and Karp, J. ACM
19 (1972), §1.2, Proposition 3, inequality (1), with `r` the residual network `N^k` and `r'` the
residual network `N^{k+1}`). -/
theorem relatesWithinSteps_source_of_shortest {p : List α} {s t : α} {L : ℕ}
    (hp : p.IsChainFromTo r s t) (hlen : p.length = L + 1)
    (hmin : ∀ k, RelatesInSteps r s t k → L ≤ k)
    (hr' : ∀ a b, r' a b → r a b ∨ (b, a) ∈ pathEdges p)
    {u : α} {k : ℕ} (hw : RelatesInSteps r' s u k) : RelatesWithinSteps r s u k := by
  induction hw with
  | refl => exact RelatesWithinSteps.refl _
  | tail a b k _ hab ih =>
    obtain ⟨j, hjk, hj⟩ := ih
    rcases hr' a b hab with h | h
    · exact ⟨j + 1, by omega, .tail _ _ _ _ hj h⟩
    · obtain ⟨i, i', hi, _, hi', hl⟩ := exists_split_of_mem_pathEdges hp h
      have := hmin _ (hj.trans hi')
      exact ⟨i, by omega, hi⟩

/-- **Distances to the sink do not decrease (abstract form of Edmonds–Karp, Proposition 3 (2)).**
Under the hypotheses of `relatesWithinSteps_source_of_shortest`, every `r'`-walk of length `k`
from `u` to `t` can be replaced by an `r`-walk of length at most `k` from `u` to `t` (Edmonds and
Karp, J. ACM 19 (1972), §1.2, Proposition 3, inequality (2)). -/
theorem relatesWithinSteps_sink_of_shortest {p : List α} {s t : α} {L : ℕ}
    (hp : p.IsChainFromTo r s t) (hlen : p.length = L + 1)
    (hmin : ∀ k, RelatesInSteps r s t k → L ≤ k)
    (hr' : ∀ a b, r' a b → r a b ∨ (b, a) ∈ pathEdges p)
    {u : α} {k : ℕ} (hw : RelatesInSteps r' u t k) : RelatesWithinSteps r u t k := by
  induction hw using RelatesInSteps.head_induction_on with
  | hrefl => exact RelatesWithinSteps.refl _
  | hhead hab hrest ih =>
    rename_i a c m
    obtain ⟨j, hjk, hj⟩ := ih
    rcases hr' a c hab with h | h
    · exact ⟨j + 1, by omega, RelatesInSteps.head _ _ _ _ h hj⟩
    · obtain ⟨i, i', hi, _, hi', hl⟩ := exists_split_of_mem_pathEdges hp h
      have := hmin _ (hi.trans hj)
      exact ⟨i', by omega, hi'⟩

end Chains

section Residual

/-- **Augmentation decreases a skew flow only against the path.** If the pair `(v, u)` is not a
step of `path`, the net change `edgeDelta path u v` that augmentation along `path` applies to
`(u, v)` is nonnegative. -/
theorem edgeDelta_nonneg_of_not_mem {V : Type*} [DecidableEq V] :
    ∀ {path : List V} {u v : V}, (v, u) ∉ pathEdges path → 0 ≤ edgeDelta path u v
  | [], _, _, _ => by simp [edgeDelta]
  | [_], _, _, _ => by simp [edgeDelta]
  | x :: y :: rest, u, v, h => by
    simp only [pathEdges, List.mem_cons, Prod.mk.injEq, not_or] at h
    have ih := edgeDelta_nonneg_of_not_mem (path := y :: rest) h.2
    have hne : ¬ (u = y ∧ v = x) := fun huv => h.1 ⟨huv.2, huv.1⟩
    simp only [edgeDelta, localDelta, hne, ite_false]
    split <;> omega

/-- **New residual arcs reverse the augmenting path (Edmonds–Karp, Proposition 2).** After
augmenting a skew flow along `path` by a nonnegative amount, every arc of the new residual graph
is an arc of the old residual graph or the reverse of a step of `path` (Edmonds and Karp, J. ACM
19 (1972), §1.2, Proposition 2). -/
theorem residualGraph_edge_augment {n : ℕ} (capacity : Fin n → Fin n → ℕ) (flow : Flow n)
    (path : List (Fin n)) {amount : ℤ} (hamount : 0 ≤ amount) {u v : Fin n}
    (h : (residualGraph capacity (augment flow path amount)).Edge u v) :
    (residualGraph capacity flow).Edge u v ∨ (v, u) ∈ pathEdges path := by
  rw [residualGraph_edge_iff] at h ⊢
  by_contra hcon
  rw [not_or, not_lt] at hcon
  have hdelta := Int.mul_nonneg hamount (edgeDelta_nonneg_of_not_mem hcon.2)
  simp only [augment] at h
  omega

/-- **Bottlenecks of residual chains are nonnegative.** If consecutive entries of `path` are
residual arcs, the bottleneck `pathBottleneck capacity flow path` is nonnegative (positive on
paths with at least one arc, zero on shorter lists). -/
theorem pathBottleneck_nonneg_of_isChain {n : ℕ} (capacity : Fin n → Fin n → ℕ)
    (flow : Flow n) : ∀ {path : List (Fin n)},
      path.IsChain (residualGraph capacity flow).Edge → 0 ≤ pathBottleneck capacity flow path
  | [], _ => by simp [pathBottleneck]
  | [_], _ => by simp [pathBottleneck]
  | [x, y], h => by
    have hxy := (List.isChain_cons_cons.mp h).1
    rw [residualGraph_edge_iff] at hxy
    simp only [pathBottleneck, residualAmount]
    omega
  | x :: y :: z :: rest, h => by
    have hxy := (List.isChain_cons_cons.mp h).1
    have ih := pathBottleneck_nonneg_of_isChain capacity flow (List.isChain_cons_cons.mp h).2
    rw [residualGraph_edge_iff] at hxy
    simp only [pathBottleneck, residualAmount] at ih ⊢
    omega

/-- **One Edmonds–Karp step does not shorten distances from the source (Proposition 3 (1)).**
For the algorithm's `step` (augmentation by the bottleneck along the shortest residual path from
`source` to `sink`, or no change when there is none), every walk of length `k` from `source` to
`u` in the new residual graph can be replaced by a walk of length at most `k` in the old one:
`δ^k(s, u) ≤ δ^{k+1}(s, u)` (Edmonds and Karp, J. ACM 19 (1972), §1.2, Proposition 3,
inequality (1)). -/
theorem walk_step_source {n : ℕ} (capacity : Fin n → Fin n → ℕ) (source sink : Fin n)
    (flow : Flow n) {u : Fin n} {k : ℕ}
    (hw : (residualGraph capacity (step capacity source sink flow)).Walk k source u) :
    RelatesWithinSteps (residualGraph capacity flow).Edge source u k := by
  unfold step at hw
  split at hw
  · exact RelatesWithinSteps.of_relatesInSteps hw
  · rename_i path hpath
    obtain ⟨hP, d, hd, hlen⟩ := shortestPath_sound hpath
    have hmin := ((distance_eq_some_iff_shortest _ _ _ _).mp hd).2
    refine relatesWithinSteps_source_of_shortest hP.1 hlen hmin ?_ hw
    intro a b hab
    exact residualGraph_edge_augment capacity flow path
      (pathBottleneck_nonneg_of_isChain capacity flow hP.1.isChain) hab

/-- **One Edmonds–Karp step does not shorten distances to the sink (Proposition 3 (2)).** For
the algorithm's `step`, every walk of length `k` from `u` to `sink` in the new residual graph can
be replaced by a walk of length at most `k` in the old one: `δ^k(u, t) ≤ δ^{k+1}(u, t)` (Edmonds
and Karp, J. ACM 19 (1972), §1.2, Proposition 3, inequality (2)). -/
theorem walk_step_sink {n : ℕ} (capacity : Fin n → Fin n → ℕ) (source sink : Fin n)
    (flow : Flow n) {u : Fin n} {k : ℕ}
    (hw : (residualGraph capacity (step capacity source sink flow)).Walk k u sink) :
    RelatesWithinSteps (residualGraph capacity flow).Edge u sink k := by
  unfold step at hw
  split at hw
  · exact RelatesWithinSteps.of_relatesInSteps hw
  · rename_i path hpath
    obtain ⟨hP, d, hd, hlen⟩ := shortestPath_sound hpath
    have hmin := ((distance_eq_some_iff_shortest _ _ _ _).mp hd).2
    refine relatesWithinSteps_sink_of_shortest hP.1 hlen hmin ?_ hw
    intro a b hab
    exact residualGraph_edge_augment capacity flow path
      (pathBottleneck_nonneg_of_isChain capacity flow hP.1.isChain) hab

/-- **Breadth-first-search distances from the source do not decrease along Edmonds–Karp.** If
`u` is at breadth-first-search distance `d'` from `source` in the residual graph after one
`step`, then it was already reachable before, at a distance `d ≤ d'` (Edmonds and Karp, J. ACM
19 (1972), §1.2, Proposition 3, inequality (1)). -/
theorem bfs_distance_source_le_step {n : ℕ} (capacity : Fin n → Fin n → ℕ)
    (source sink : Fin n) (flow : Flow n) {u : Fin n} {d' : ℕ}
    (hd' : (bfs (residualGraph capacity (step capacity source sink flow)) source).distance u =
      some d') :
    ∃ d, (bfs (residualGraph capacity flow) source).distance u = some d ∧ d ≤ d' := by
  have hw := ((distance_eq_some_iff_shortest _ _ _ _).mp hd').1
  obtain ⟨m, hm, hwm⟩ := walk_step_source capacity source sink flow hw
  obtain ⟨d, hd⟩ :=
    (distance_present_iff_reachable _ _ _).mpr (reachable_iff_exists_walk.mpr ⟨m, hwm⟩)
  exact ⟨d, hd, le_trans (((distance_eq_some_iff_shortest _ _ _ _).mp hd).2 m hwm) hm⟩

/-- **Breadth-first-search distances to the sink do not decrease along Edmonds–Karp.** Distances
to `sink` are computed, as in the algorithm, by breadth-first search from `sink` in the
transposed residual graph. If `u` is at distance `d'` from `sink` there after one `step`, it was
at a distance `d ≤ d'` before (Edmonds and Karp, J. ACM 19 (1972), §1.2, Proposition 3,
inequality (2)). -/
theorem bfs_distance_sink_le_step {n : ℕ} (capacity : Fin n → Fin n → ℕ)
    (source sink : Fin n) (flow : Flow n) {u : Fin n} {d' : ℕ}
    (hd' : (bfs (residualGraph capacity (step capacity source sink flow)).transpose sink).distance
      u = some d') :
    ∃ d, (bfs (residualGraph capacity flow).transpose sink).distance u = some d ∧ d ≤ d' := by
  have hw := walk_transpose_iff.mp ((distance_eq_some_iff_shortest _ _ _ _).mp hd').1
  obtain ⟨m, hm, hwm⟩ := walk_step_sink capacity source sink flow hw
  have hwm' := walk_transpose_iff.mpr hwm
  obtain ⟨d, hd⟩ :=
    (distance_present_iff_reachable _ _ _).mpr (reachable_iff_exists_walk.mpr ⟨m, hwm'⟩)
  exact ⟨d, hd, le_trans (((distance_eq_some_iff_shortest _ _ _ _).mp hd).2 m hwm') hm⟩

end Residual

end Cslib.Algorithms.Lean.EdmondsKarp
