/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Basic
public import Mathlib.Data.Rat.Defs

/-!
# Karp's characterization of the minimum cycle mean

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

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BellmanFord

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

/-- **Karp's minimum cycle mean theorem.** Let the digraph of `edges`, on `n` vertices, be strongly
connected, let `λ` be its minimum cycle mean, and let `s` be a vertex. Then
`λ = min_v max_{0 ≤ k ≤ n - 1} (F_n(v) - F_k(v)) / (n - k)`, in the following form: every vertex
`v` with `F_n(v)` finite has an index `k < n` with `F_k(v)` finite and
`(F_n(v) - F_k(v)) / (n - k) ≥ λ`; and some vertex `v` with `F_n(v)` finite has
`(F_n(v) - F_k(v)) / (n - k) ≤ λ` for every `k < n` with `F_k(v)` finite (Karp, Discrete
Mathematics 23 (1978), Theorem 1, for integer weights). -/
theorem_wanted karp_minCycleMean {n : ℕ} (edges : List (Edge n))
    (strong : ∀ u v, (toDirectedAdjacency edges).Reachable u v) (s : Fin n) (lam : ℚ)
    (hlam : IsMinCycleMean edges lam) :
    (∀ v x, IsMinWalkWeight edges s v n x →
      ∃ k < n, ∃ y, IsMinWalkWeight edges s v k y ∧
        lam ≤ ((x - y : ℤ) : ℚ) / ((n - k : ℕ) : ℚ)) ∧
    ∃ v x, IsMinWalkWeight edges s v n x ∧
      ∀ k < n, ∀ y, IsMinWalkWeight edges s v k y →
        ((x - y : ℤ) : ℚ) / ((n - k : ℕ) : ℚ) ≤ lam

end Cslib.Algorithms.Lean.BellmanFord
